local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local ServerStorage = game:GetService("ServerStorage")
local Debris = game:GetService("Debris")

local turretFolder = workspace.Turrets
local shellTemplate = ServerStorage.Shell

local shellFolder = Instance.new("Folder")
shellFolder.Name = "Shells"
shellFolder.Parent = workspace

local defaultRange = 140
local turnSpeed = math.rad(150)
local idleSpin = math.rad(25)
local minPitch = math.rad(-20)
local maxPitch = math.rad(75)
local scanInterval = 0.25
local fireCooldown = 1.1
local shellSpeed = 130
local shellRadius = 0.6
local maxBounces = 2
local bounceDamping = 0.55
local shellLifetime = 6
local blastRadius = 12
local maxDamage = 45
local blastPush = 55

local gravity = Vector3.new(0, -workspace.Gravity, 0)
local aimThreshold = math.cos(math.rad(3)) -- compared against a dot product so we never need acos
local hiddenCFrame = CFrame.new(0, 10e8, 0) -- pooled shells wait up here, reparenting would re-replicate them
local fullCircle = math.pi * 2

local rayParams = RaycastParams.new()
rayParams.FilterType = Enum.RaycastFilterType.Exclude
rayParams.FilterDescendantsInstances = {turretFolder, shellFolder}

local overlapParams = OverlapParams.new()
overlapParams.FilterType = Enum.RaycastFilterType.Exclude
overlapParams.FilterDescendantsInstances = {turretFolder, shellFolder}

-- everything that moves this frame goes in here and gets moved with one BulkMoveTo
local movingParts = {}
local movingCFrames = {}

local function queueMove(part, cframe)
	local i = #movingParts + 1
	movingParts[i] = part
	movingCFrames[i] = cframe
end

-- soonest t > 0 where |offset + targetVelocity * t| = speed * t
local function getInterceptTime(offset, targetVelocity, speed)
	local a = targetVelocity:Dot(targetVelocity) - speed * speed
	local b = 2 * offset:Dot(targetVelocity)
	local c = offset:Dot(offset)

	if math.abs(a) < 1e-6 then
		-- target is exactly as fast as the shell, so it's linear
		if math.abs(b) < 1e-6 then
			return nil
		end
		local t = -c / b
		return if t > 0 then t else nil
	end

	local discriminant = b * b - 4 * a * c
	if discriminant < 0 then
		return nil -- target is outrunning the shell
	end

	local root = math.sqrt(discriminant)
	local t1 = (-b - root) / (2 * a)
	local t2 = (-b + root) / (2 * a)
	local t = math.min(t1, t2)
	if t <= 0 then
		t = math.max(t1, t2)
	end
	return if t > 0 then t else nil
end

local function getLaunchVelocity(origin, targetPosition, targetVelocity)
	local t = getInterceptTime(targetPosition - origin, targetVelocity, shellSpeed)
	if not t then
		return nil
	end

	local hitPosition = targetPosition + targetVelocity * t
	-- p = o + vt + gt^2/2 solved for v, so the shell lands there after exactly t seconds
	return (hitPosition - origin) / t - gravity * (0.5 * t)
end

local function reflect(velocity, normal)
	return velocity - normal * (2 * velocity:Dot(normal))
end

-- turns the short way around, capped at maxStep
local function turnTowards(angle, goal, maxStep)
	local diff = (goal - angle + math.pi) % fullCircle - math.pi
	return (angle + math.clamp(diff, -maxStep, maxStep)) % fullCircle
end

local function getHumanoid(part)
	local model = part:FindFirstAncestorOfClass("Model")
	return if model then model:FindFirstChildOfClass("Humanoid") else nil
end

local function getAliveHumanoid(player)
	local character = player.Character
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")
	if humanoid and humanoid.Health > 0 then
		return humanoid
	end
	return nil
end

local function explode(position)
	local explosion = Instance.new("Explosion")
	explosion.Position = position
	explosion.BlastRadius = blastRadius
	explosion.BlastPressure = 0 -- only used for the effect, damage and knockback are handled below
	explosion.DestroyJointRadiusPercent = 0
	explosion.Parent = workspace
	Debris:AddItem(explosion, 2)

	local hitHumanoids = {}
	local pushedParts = {}

	for _, part in workspace:GetPartBoundsInRadius(position, blastRadius, overlapParams) do
		local humanoid = getHumanoid(part)

		if humanoid then
			if not hitHumanoids[humanoid] then
				hitHumanoids[humanoid] = true
				local root = humanoid.RootPart
				local distance = if root then (root.Position - position).Magnitude else blastRadius
				humanoid:TakeDamage(maxDamage * (1 - math.min(distance / blastRadius, 1)))
			end
		elseif not part.Anchored then
			local root = part.AssemblyRootPart
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

local Shell = {}
Shell.__index = Shell

local shellPool = {}
local activeShells = {}

function Shell.new()
	local part = shellTemplate:Clone()
	part.CFrame = hiddenCFrame
	part.Parent = shellFolder

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
	local shell = table.remove(shellPool) or Shell.new()
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

	-- vt + at^2/2 is exact for constant gravity, so the arc is the same at any framerate
	local move = self.velocity * dt + gravity * (0.5 * dt * dt)
	local hit = workspace:Spherecast(self.position, shellRadius, move, rayParams)

	if not hit then
		self.position += move
		self.velocity += gravity * dt
		return true
	end

	if getHumanoid(hit.Instance) or self.bounces >= maxBounces then
		explode(hit.Position)
		return false
	end

	-- velocity at the moment it hit, not at the end of the frame
	local impactVelocity = self.velocity + gravity * (dt * hit.Distance / move.Magnitude)
	self.velocity = reflect(impactVelocity, hit.Normal) * bounceDamping
	self.position += move.Unit * hit.Distance + hit.Normal * 0.05 -- spherecasts ignore parts they start inside, so back off a bit
	self.bounces += 1
	return true
end

function Shell:Free()
	self.trail.Enabled = false
	table.insert(shellPool, self)
	queueMove(self.part, hiddenCFrame)
end

local function updateShells(dt)
	local i = 1
	while i <= #activeShells do
		local shell = activeShells[i]

		if shell:Step(dt) then
			queueMove(shell.part, CFrame.new(shell.position))
			i += 1
		else
			-- swap in the last shell and pop, order doesn't matter so this beats table.remove
			activeShells[i] = activeShells[#activeShells]
			activeShells[#activeShells] = nil
			shell:Free()
		end
	end
end

local Turret = {}
Turret.__index = Turret

local turrets = {}

function Turret.new(model)
	local head = model.Head
	local barrel = model.Barrel

	local self = setmetatable({}, Turret)
	self.head = head
	self.barrel = barrel
	self.rest = head.CFrame -- yaw and pitch are applied on top of the pose it was built in
	self.aim = head.CFrame
	self.barrelOffset = head.CFrame:ToObjectSpace(barrel.CFrame)
	self.muzzleOffset = head.CFrame:ToObjectSpace(barrel.Muzzle.WorldCFrame)
	self.range = model:GetAttribute("Range") or defaultRange
	self.yaw = 0
	self.pitch = 0
	self.cooldown = 0
	self.scanTimer = math.random() * scanInterval -- spread scans out so every turret doesn't raycast on the same frame
	self.target = nil
	return self
end

function Turret:FindTarget()
	local origin = self.rest.Position
	local closest = nil
	local closestDistance = self.range

	for _, player in Players:GetPlayers() do
		local humanoid = getAliveHumanoid(player)
		local root = humanoid and humanoid.RootPart
		local character = humanoid and humanoid.Parent

		-- forcefield players can't take damage, no point wasting a shot
		if root and not character:FindFirstChildOfClass("ForceField") then
			local offset = root.Position - origin
			local distance = offset.Magnitude

			if distance < closestDistance then
				local hit = workspace:Raycast(origin, offset, rayParams)
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
		self.scanTimer += scanInterval
		self.target = self:FindTarget()
	end

	local launchVelocity = nil
	local target = self.target

	if target and target:IsDescendantOf(workspace) then
		local muzzle = (self.aim * self.muzzleOffset).Position
		local velocity = target.AssemblyLinearVelocity
		-- ignore Y, jumping players come back down so predicting it just overshoots
		launchVelocity = getLaunchVelocity(muzzle, target.Position, Vector3.new(velocity.X, 0, velocity.Z))
	end

	local aimDirection = nil
	local goalYaw = self.yaw + idleSpin * dt
	local goalPitch = 0

	if launchVelocity then
		aimDirection = launchVelocity.Unit
		local localDirection = self.rest:VectorToObjectSpace(aimDirection)
		local flatLength = Vector2.new(localDirection.X, localDirection.Z).Magnitude
		goalYaw = math.atan2(-localDirection.X, -localDirection.Z) -- forward is -Z
		goalPitch = math.clamp(math.atan2(localDirection.Y, flatLength), minPitch, maxPitch)
	end

	local maxTurn = turnSpeed * dt
	self.yaw = turnTowards(self.yaw, goalYaw, maxTurn)
	self.pitch += math.clamp(goalPitch - self.pitch, -maxTurn, maxTurn)

	-- head only spins, barrel spins and tilts
	local yawCFrame = self.rest * CFrame.Angles(0, self.yaw, 0)
	self.aim = yawCFrame * CFrame.Angles(self.pitch, 0, 0)
	queueMove(self.head, yawCFrame)
	queueMove(self.barrel, self.aim * self.barrelOffset)

	-- wait for the barrel to actually line up before shooting
	if aimDirection and self.cooldown <= 0 and self.aim.LookVector:Dot(aimDirection) >= aimThreshold then
		self.cooldown = fireCooldown
		getShell():Launch((self.aim * self.muzzleOffset).Position, launchVelocity)
	end
end

local function addTurret(model)
	if model:IsA("Model") then
		turrets[model] = Turret.new(model)
	end
end

turretFolder.ChildAdded:Connect(addTurret)
turretFolder.ChildRemoved:Connect(function(model)
	turrets[model] = nil
end)

for _, model in turretFolder:GetChildren() do
	addTurret(model)
end

local playerStats = {}

local function onPlayerAdded(player)
	local leaderstats = Instance.new("Folder")
	leaderstats.Name = "leaderstats"

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
	playerStats[player] = nil
end)

for _, player in Players:GetPlayers() do
	onPlayerAdded(player)
end

local scoreTimer = 0

RunService.Heartbeat:Connect(function(dt)
	for _, turret in turrets do
		turret:Update(dt)
	end
	updateShells(dt)

	if #movingParts > 0 then
		workspace:BulkMoveTo(movingParts, movingCFrames, Enum.BulkMoveMode.FireCFrameChanged)
		table.clear(movingParts)
		table.clear(movingCFrames)
	end

	scoreTimer += dt
	if scoreTimer >= 1 then
		scoreTimer -= 1

		for player, stats in playerStats do
			if getAliveHumanoid(player) then
				stats.survived.Value += 1
				stats.best.Value = math.max(stats.best.Value, stats.survived.Value)
			end
		end
	end
end)
