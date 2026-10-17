-- Connected Discord-GitHub
--[[
	turret system

	turrets live in workspace.Turrets as models (Head, Barrel, and a Muzzle attachment on the barrel).
	each one picks the closest player it can see, works out where that player will be by the time a
	shell gets there, turns toward that at a capped speed and fires once the barrel is lined up.

	shells aren't real physics objects. they're anchored parts that I move myself every frame using
	spherecasts, so I control gravity and bouncing exactly, they can't get stuck on anything, and the
	server never hands them to a client for network ownership.

	everything runs off one Heartbeat connection at the bottom. turrets and shells don't set .CFrame
	during the frame, they add to a queue and one BulkMoveTo call moves all of it at the end.
]]

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local ServerStorage = game:GetService("ServerStorage")
local Debris = game:GetService("Debris")

local turretFolder = workspace.Turrets
local shellTemplate = ServerStorage.Shell

local shellFolder = Instance.new("Folder")
shellFolder.Name = "Shells"
shellFolder.Parent = workspace

-- tuning
local defaultRange = 140
local turnSpeed = math.rad(150) -- per second, capped so you can actually juke a turret by running around it
local idleSpin = math.rad(25) -- slow spin when there's no target so it looks like it's searching
local minPitch = math.rad(-20) -- any lower and the muzzle dips below the mount, so a shell could spawn inside it
local maxPitch = math.rad(75)
local scanInterval = 0.25 -- finding a target raycasts once per player, no reason to do that every frame
local fireCooldown = 1.1
local shellSpeed = 130
local shellRadius = 0.6 -- same radius I spherecast with, so the hitbox matches the ball you see
local maxBounces = 2
local bounceDamping = 0.55 -- fraction of speed kept after a bounce
local shellLifetime = 6 -- safety net for shells that fly off the map
local blastRadius = 12
local maxDamage = 45
local blastPush = 55 -- velocity (studs/s) a loose prop gets at the center of a blast

local gravity = Vector3.new(0, -workspace.Gravity, 0) -- read from workspace so shells fall the same way players do
local aimThreshold = math.cos(math.rad(3)) -- compared against a dot product so we never need acos
local hiddenCFrame = CFrame.new(0, 10e8, 0) -- pooled shells wait up here, reparenting would re-replicate them
local fullCircle = math.pi * 2

-- made once and reused instead of every cast. excluding the two folders (instead of individual parts)
-- means turrets added later are already covered, and shells can't hit each other or the turret that fired them
local rayParams = RaycastParams.new()
rayParams.FilterType = Enum.RaycastFilterType.Exclude
rayParams.FilterDescendantsInstances = {turretFolder, shellFolder}

-- explosions need the same filter, but GetPartBoundsInRadius takes OverlapParams instead
local overlapParams = OverlapParams.new()
overlapParams.FilterType = Enum.RaycastFilterType.Exclude
overlapParams.FilterDescendantsInstances = {turretFolder, shellFolder}

-- everything that moves this frame goes in here and gets moved with one BulkMoveTo.
-- that's one engine call instead of setting .CFrame on every head, barrel and shell separately
local movingParts = {}
local movingCFrames = {}

local function queueMove(part, cframe)
	local i = #movingParts + 1 -- same index for both arrays so they can't get out of sync
	movingParts[i] = part
	movingCFrames[i] = cframe
end

-- the turret has to know how long the shell will be in the air before it knows where to aim.
-- if the target keeps moving at the same velocity, the shell meets it when
-- |offset + targetVelocity * t| = speed * t. squaring both sides turns that into a normal
-- quadratic a*t^2 + b*t + c = 0, which is what a, b and c are below
local function getInterceptTime(offset, targetVelocity, speed)
	local a = targetVelocity:Dot(targetVelocity) - speed * speed
	local b = 2 * offset:Dot(targetVelocity)
	local c = offset:Dot(offset)

	if math.abs(a) < 1e-6 then
		-- target is exactly as fast as the shell, the t^2 term cancels out so it's linear (and dividing by a would blow up)
		if math.abs(b) < 1e-6 then
			return nil
		end
		local t = -c / b
		return if t > 0 then t else nil
	end

	local discriminant = b * b - 4 * a * c
	if discriminant < 0 then
		return nil -- no real answer means the target is outrunning the shell
	end

	-- two answers. the smaller positive one is the earliest hit, which gives the player less time to change direction
	local root = math.sqrt(discriminant)
	local t1 = (-b - root) / (2 * a)
	local t2 = (-b + root) / (2 * a)
	local t = math.min(t1, t2)
	if t <= 0 then
		t = math.max(t1, t2) -- the earlier one is in the past, so the later one is the only real hit
	end
	return if t > 0 then t else nil
end

-- t only says when the shell arrives, this turns it into an actual launch velocity.
-- the shell's position over time is p = o + v*t + 0.5*g*t^2. I want p to equal hitPosition at time t,
-- so solving for v gives (hitPosition - o)/t - 0.5*g*t. the second part just aims higher to cancel the drop.
-- the real launch speed ends up a bit over shellSpeed because of that, but flight time is still exactly t
local function getLaunchVelocity(origin, targetPosition, targetVelocity)
	local t = getInterceptTime(targetPosition - origin, targetVelocity, shellSpeed)
	if not t then
		return nil
	end

	local hitPosition = targetPosition + targetVelocity * t -- where the target will be when the shell gets there
	return (hitPosition - origin) / t - gravity * (0.5 * t)
end

-- velocity:Dot(normal) is how much of the velocity goes into the surface. taking that away twice
-- flips it to come out the other side, same as a mirror reflection
local function reflect(velocity, normal)
	return velocity - normal * (2 * velocity:Dot(normal))
end

-- yaw is an angle, so going from 350 to 10 degrees should turn 20 degrees forward, not 340 back.
-- adding pi, taking % 2pi and subtracting pi wraps the difference into -pi..pi (luau's % is floored so
-- negatives work). the last % keeps the stored yaw from growing forever while it idle spins
local function turnTowards(angle, goal, maxStep)
	local diff = (goal - angle + math.pi) % fullCircle - math.pi
	return (angle + math.clamp(diff, -maxStep, maxStep)) % fullCircle
end

-- a hit can be on a limb, an accessory handle or a tool. none of those are Models, so the first
-- Model up the tree is the character
local function getHumanoid(part)
	local model = part:FindFirstAncestorOfClass("Model")
	return if model then model:FindFirstChildOfClass("Humanoid") else nil
end

-- targeting and scoring both use this, so "alive" means the same thing in both places
local function getAliveHumanoid(player)
	local character = player.Character
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")
	if humanoid and humanoid.Health > 0 then
		return humanoid
	end
	return nil
end

local function explode(position)
	-- the Explosion instance is only for the effect and sound. with BlastPressure and DestroyJointRadiusPercent
	-- at 0 it doesn't fling or kill anything itself, so the damage falloff and knockback below are fully mine
	local explosion = Instance.new("Explosion")
	explosion.Position = position
	explosion.BlastRadius = blastRadius
	explosion.BlastPressure = 0
	explosion.DestroyJointRadiusPercent = 0
	explosion.Parent = workspace
	Debris:AddItem(explosion, 2) -- cleans it up later without yielding this function

	-- a character has a bunch of parts inside the radius, so these sets stop the same
	-- humanoid getting damaged (or the same prop getting pushed) more than once
	local hitHumanoids = {}
	local pushedParts = {}

	for _, part in workspace:GetPartBoundsInRadius(position, blastRadius, overlapParams) do
		local humanoid = getHumanoid(part)

		if humanoid then
			if not hitHumanoids[humanoid] then
				hitHumanoids[humanoid] = true
				local root = humanoid.RootPart
				local distance = if root then (root.Position - position).Magnitude else blastRadius
				-- full damage at the center, 0 at the edge. TakeDamage respects forcefields, setting Health directly wouldn't
				humanoid:TakeDamage(maxDamage * (1 - math.min(distance / blastRadius, 1)))
			end
		elseif not part.Anchored then
			local root = part.AssemblyRootPart -- impulses act on the whole assembly, so I push the root once
			if root and not pushedParts[root] then
				pushedParts[root] = true

				if root:CanSetNetworkOwnership() then
					root:SetNetworkOwner(nil) -- if a client owns it the server's impulse gets ignored
				end

				local offset = root.Position - position
				local falloff = 1 - math.min(offset.Magnitude / blastRadius, 1)
				local direction = (offset + Vector3.new(0, blastRadius / 2, 0)).Unit -- bias upward so props fly instead of sliding
				root:ApplyImpulse(direction * blastPush * falloff * root.AssemblyMass) -- times mass so light and heavy props react the same
			end
		end
	end
end

-- shells are pooled. creating and destroying a part every shot is slow and spams replication,
-- so finished shells go back in shellPool and get reused for the next shot
local Shell = {}
Shell.__index = Shell

local shellPool = {}
local activeShells = {}

function Shell.new()
	local part = shellTemplate:Clone()
	part.CFrame = hiddenCFrame
	part.Parent = shellFolder

	-- position and velocity are the real simulation, the part just gets moved to match them
	local self = setmetatable({}, Shell)
	self.part = part
	self.trail = part.Trail
	self.position = Vector3.zero
	self.velocity = Vector3.zero
	self.age = 0
	self.bounces = 0
	return self
end

local function getShell()
	local shell = table.remove(shellPool) or Shell.new() -- popping from the end is O(1), and only builds a new one if the pool is empty
	table.insert(activeShells, shell)
	return shell
end

function Shell:Launch(origin, velocity)
	self.position = origin
	self.velocity = velocity
	self.age = 0
	self.bounces = 0
	self.part.CFrame = CFrame.new(origin) -- move it before turning the trail on or it streaks in from the hidden spot
	self.trail.Enabled = true
end

-- returns false when the shell is done and should go back in the pool
function Shell:Step(dt)
	self.age += dt
	if self.age > shellLifetime then
		return false
	end

	-- vt + at^2/2 is the exact distance for constant gravity. plain v*dt would change the arc depending on framerate
	local move = self.velocity * dt + gravity * (0.5 * dt * dt)
	-- spherecast instead of a raycast so the whole ball is the hitbox. a thin ray could slip past a limb or through a gap
	local hit = workspace:Spherecast(self.position, shellRadius, move, rayParams)

	if not hit then
		self.position += move
		self.velocity += gravity * dt
		return true
	end

	-- players always set it off, walls and floors only do once it's out of bounces
	if getHumanoid(hit.Instance) or self.bounces >= maxBounces then
		explode(hit.Position)
		return false
	end

	-- hit.Distance / move.Magnitude is roughly how far into the frame the hit happened,
	-- so this is the velocity at the moment of impact instead of at the end of the frame
	local impactVelocity = self.velocity + gravity * (dt * hit.Distance / move.Magnitude)
	self.velocity = reflect(impactVelocity, hit.Normal) * bounceDamping
	self.position += move.Unit * hit.Distance + hit.Normal * 0.05 -- spherecasts ignore parts they start inside, so back off a bit
	self.bounces += 1
	return true
end

function Shell:Free()
	self.trail.Enabled = false -- off before it moves so it doesn't draw a line up to hiddenCFrame
	table.insert(shellPool, self)
	queueMove(self.part, hiddenCFrame) -- parked through the same BulkMoveTo as everything else
end

local function updateShells(dt)
	local i = 1
	while i <= #activeShells do -- while instead of for because the array shrinks as I go through it
		local shell = activeShells[i]

		if shell:Step(dt) then
			queueMove(shell.part, CFrame.new(shell.position))
			i += 1
		else
			-- swap in the last shell and pop, order doesn't matter so this beats table.remove shifting everything
			activeShells[i] = activeShells[#activeShells]
			activeShells[#activeShells] = nil
			shell:Free()
			-- i stays the same because a different shell is in this slot now and it still needs to step
		end
	end
end

-- one Turret object per model in workspace.Turrets
local Turret = {}
Turret.__index = Turret

local turrets = {}

function Turret.new(model)
	local head = model.Head
	local barrel = model.Barrel

	local self = setmetatable({}, Turret)
	self.head = head
	self.barrel = barrel
	self.rest = head.CFrame -- the pose it was built in, yaw and pitch get applied on top so it can face any way in studio
	self.aim = head.CFrame
	-- where the barrel and muzzle sit relative to the head. storing these offsets means any turret model works
	-- and nothing about its size is hardcoded
	self.barrelOffset = head.CFrame:ToObjectSpace(barrel.CFrame)
	self.muzzleOffset = head.CFrame:ToObjectSpace(barrel.Muzzle.WorldCFrame)
	self.range = model:GetAttribute("Range") or defaultRange -- optional per-turret override set in studio
	self.yaw = 0
	self.pitch = 0
	self.cooldown = 0
	self.scanTimer = math.random() * scanInterval -- spread scans out so every turret doesn't raycast on the same frame
	self.target = nil
	return self
end

-- closest player that's alive, not forcefielded, in range, and actually visible
function Turret:FindTarget()
	local origin = self.rest.Position
	local closest = nil
	local closestDistance = self.range -- starting at range means anyone further away fails the same check

	for _, player in Players:GetPlayers() do
		local humanoid = getAliveHumanoid(player)
		local root = humanoid and humanoid.RootPart
		local character = humanoid and humanoid.Parent

		-- forcefield players can't take damage, no point wasting a shot
		if root and not character:FindFirstChildOfClass("ForceField") then
			local offset = root.Position - origin
			local distance = offset.Magnitude

			if distance < closestDistance then -- distance first since it's way cheaper than the raycast
				local hit = workspace:Raycast(origin, offset, rayParams)
				-- if the first thing the ray touches is part of the character, nothing is in between
				if not hit or hit.Instance:IsDescendantOf(character) then
					closest = root
					closestDistance = distance
				end
			end
		end
	end

	return closest
end

function Turret:Update(dt)
	self.cooldown = math.max(self.cooldown - dt, 0)
	self.scanTimer -= dt

	if self.scanTimer <= 0 then
		self.scanTimer += scanInterval -- += instead of = so each turret keeps its random offset
		self.target = self:FindTarget()
	end

	local launchVelocity = nil
	local target = self.target

	if target and target:IsDescendantOf(workspace) then -- the target could have respawned since the last scan
		local muzzle = (self.aim * self.muzzleOffset).Position -- aim from the muzzle since that's where the shell actually starts
		local velocity = target.AssemblyLinearVelocity
		-- ignore Y, jumping players come back down so predicting it just overshoots
		launchVelocity = getLaunchVelocity(muzzle, target.Position, Vector3.new(velocity.X, 0, velocity.Z))
	end

	-- defaults are the idle spin, they get replaced if there's a shot to line up
	local aimDirection = nil
	local goalYaw = self.yaw + idleSpin * dt
	local goalPitch = 0

	if launchVelocity then
		aimDirection = launchVelocity.Unit
		-- converted into the turret's own space so yaw and pitch come out of plain trig even if the turret is rotated
		local localDirection = self.rest:VectorToObjectSpace(aimDirection)
		local flatLength = Vector2.new(localDirection.X, localDirection.Z).Magnitude
		goalYaw = math.atan2(-localDirection.X, -localDirection.Z) -- forward is -Z
		-- atan2 instead of asin(Y) because rounding can push Y a hair past 1 and asin would return NaN
		goalPitch = math.clamp(math.atan2(localDirection.Y, flatLength), minPitch, maxPitch)
	end

	local maxTurn = turnSpeed * dt -- times dt so it turns at the same speed no matter the server framerate
	self.yaw = turnTowards(self.yaw, goalYaw, maxTurn)
	self.pitch += math.clamp(goalPitch - self.pitch, -maxTurn, maxTurn) -- pitch is clamped so it never wraps, no need for turnTowards

	-- head only spins, barrel spins and tilts. yaw goes first so pitch always tilts around the barrel's own sideways axis
	local yawCFrame = self.rest * CFrame.Angles(0, self.yaw, 0)
	self.aim = yawCFrame * CFrame.Angles(self.pitch, 0, 0)
	queueMove(self.head, yawCFrame)
	queueMove(self.barrel, self.aim * self.barrelOffset)

	-- the dot of two unit vectors is the cos of the angle between them, so this only fires once the
	-- barrel is actually within 3 degrees of the shot. if the shot needs a pitch past the limits it never lines up
	if aimDirection and self.cooldown <= 0 and self.aim.LookVector:Dot(aimDirection) >= aimThreshold then
		self.cooldown = fireCooldown
		getShell():Launch((self.aim * self.muzzleOffset).Position, launchVelocity) -- muzzle recalculated since the pose just changed
	end
end

local function addTurret(model)
	if model:IsA("Model") then
		turrets[model] = Turret.new(model)
	end
end

-- turrets can be added or deleted while the game is running. removing one just drops the reference,
-- its parts go away with the model
turretFolder.ChildAdded:Connect(addTurret)
turretFolder.ChildRemoved:Connect(function(model)
	turrets[model] = nil
end)

for _, model in turretFolder:GetChildren() do -- ChildAdded won't fire for turrets that were already there
	addTurret(model)
end

local playerStats = {}

local function onPlayerAdded(player)
	local leaderstats = Instance.new("Folder")
	leaderstats.Name = "leaderstats" -- has to be exactly this for the default player list to show it

	local survived = Instance.new("IntValue")
	survived.Name = "Survived"
	survived.Parent = leaderstats

	local best = Instance.new("IntValue")
	best.Name = "Best"
	best.Parent = leaderstats

	leaderstats.Parent = player
	playerStats[player] = {survived = survived, best = best}

	-- reset on respawn, not on death, so you can still see how long you lasted
	player.CharacterAdded:Connect(function()
		survived.Value = 0
	end)
end

Players.PlayerAdded:Connect(onPlayerAdded)
Players.PlayerRemoving:Connect(function(player)
	playerStats[player] = nil -- otherwise the table keeps players who left forever
end)

for _, player in Players:GetPlayers() do -- anyone who joined before this script ran
	onPlayerAdded(player)
end

local scoreTimer = 0

-- everything runs from this one connection instead of one per turret or shell
RunService.Heartbeat:Connect(function(dt)
	for _, turret in turrets do
		turret:Update(dt)
	end
	updateShells(dt) -- after turrets so a shell fired this frame also gets stepped and drawn this frame

	if #movingParts > 0 then
		-- FireCFrameChanged skips the other property signals since nothing listens to them
		workspace:BulkMoveTo(movingParts, movingCFrames, Enum.BulkMoveMode.FireCFrameChanged)
		table.clear(movingParts) -- clear keeps the memory allocated so the arrays aren't rebuilt every frame
		table.clear(movingCFrames)
	end

	scoreTimer += dt
	if scoreTimer >= 1 then
		scoreTimer -= 1 -- subtract instead of resetting so leftover time carries over and the score doesn't fall behind

		for player, stats in playerStats do
			if getAliveHumanoid(player) then
				stats.survived.Value += 1
				stats.best.Value = math.max(stats.best.Value, stats.survived.Value)
			end
		end
	end
end)
