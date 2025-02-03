--[[
    Custom projectile Aimbot for Lmaobox
    author:
    https://github.com/titaniummachine1

    credit for proof of concept:
    https://github.com/lnx00

    credit for help with config and visuals:
    https://github.com/Muqa1

    forked by navet
    https://github.com/uosq
]]

local Menu = { -- this is the config that will be loaded every time u load the script

   Main = {
      triggerbot = false,
      triggerfov = 2,
      MinDistance = 100,
      MaxDistance = 1500,
      MinHitchance = 40,
   },

   Advanced = {
      SplashPrediction = true,
      SplashAccuracy = 6,
      PredTicks = 77,
      Hitchance_Accuracy = 17,
      AccuracyWeight = 20,
      StrafePrediction = true,
      StrafeSamples = 10,
      ProjectileSegments = 7,
   },

   Visuals = {
      Active = true,
      VisualizePath = true,
      Path_styles = { "Line", "Alt Line", "Dashed" },
      Path_styles_selected = 2,
      VisualizeHitchance = false,
      VisualizeProjectile = false,
      VisualizeHitPos = false,
      Crosshair = false,
      NccPred = false
   },
}

--- download my general purpose lib straight from the repo
---@module "ngl"
local ngl = load(http.Get("https://raw.githubusercontent.com/uosq/lbox-ngl-lib/refs/heads/main/ngl.lua"))()

--- download my ui lib straight from the repo
---@module "source"
--local alib = load(http.Get("https://raw.githubusercontent.com/uosq/lbox-alib/refs/heads/main/alib.lua"))()

--local screenW, screenH = draw.GetScreenSize()
--local centerX, centerY = math.floor(screenW / 2), math.floor(screenH / 2)

--local window = {}
--window.width, window.height = 300, 300
--window.x, window.y = centerX - math.floor(window.width / 2), centerY - math.floor(window.height / 2)

---TODO: make the window

---@class AimTarget
---@field entity Entity
---@field angles EulerAngles
---@field factor number Its the fov

---@class StrafeResult
---@field currentPos Vector3
---@field deltaAngle number
---@field predictedPos Vector3
---@field strafeCenter Vector3
---@field moving boolean

local function isNaN(number) return number ~= number end

--- checks to see if x,y,z are valid
---@param vec Vector3
local function validateVector(vec)
   if not vec then return false end
   return type(vec.x) == "number" and type(vec.y) == "number" and type(vec.z) == "number" and
       not isNaN(vec.x) and not isNaN(vec.y) and not isNaN(vec.z)
end

local Hitbox = {
   Head = 1,
   Neck = 2,
   Pelvis = 4,
   Body = 5,
   Chest = 7,
   Feet = 11,
}

-- Cache API calls for optimization
local math = math
local engine = engine
local globals = globals
local table = table
local vector = vector
local input = input
local gui = gui
local entities = entities

local math_atan = math.atan
local math_cos = math.cos
local math_sin = math.sin
local math_sqrt = math.sqrt
local math_floor = math.floor
local math_rad = math.rad
local math_deg = math.deg
local math_acos = math.acos
local math_abs = math.abs
local math_min = math.min
local math_exp = math.exp
local math_max = math.max

local TickInterval = globals.TickInterval

local TraceLine = engine.TraceLine
local TraceHull = engine.TraceHull

local GetConVar = client.GetConVar
local WorldToScreen = client.WorldToScreen

local FindByClass = entities.FindByClass

local ipairs = ipairs

local draw_Line = draw.Line
local draw_Text = draw.Text
local draw_FilledRect = draw.FilledRect

local vectorDistance = vector.Distance

local tableInsert = table.insert
local tableRemove = table.remove
local tostring = tostring

local M_RADPI = 180 / math.pi

local latency, lerp, strafeAngles, hitChance, lastPosition, priorPrediction
local hitChanceRecords, vPath, vHitbox, MAX_ANGLE_HISTORY, MAX_CENTER_HISTORY
local strafeAngleHistories, centerHistories = {},
    {} --- history of strafe angles for each player, and history of center directions for each player

latency, lerp, hitChance = 0, 0, 0
lastPosition, priorPrediction, hitChanceRecords, vPath = {}, {}, {}, {}
---@type {}
strafeAngles = {}

MAX_ANGLE_HISTORY = Menu.Advanced.StrafeSamples
MAX_CENTER_HISTORY = 5

--- what are these magical numbers?
--- StudioBBox Mins and Maxs?
vHitbox = { Vector3(-22, -22, 0), Vector3(22, 22, 80) }

local vUp = Vector3(0, 0, 1)
local GROUND_COLLISION_ANGLE_LOW = 45
local GROUND_COLLISION_ANGLE_HIGH = 60
local FORWARD_COLLISION_ANGLE = 55

local projectileSimulation = {}
local projectileSimulation2 = Vector3()

local EMPTY_VECTOR = Vector3() -- Represents an empty vector for zero velocity cases

local currentTarget = nil

local MASK_PLAYERSOLID = (MASK_SHOT_HULL | CONTENTS_GRATE)
local FULL_HIT_FRACTION = 1.0     -- Represents a full hit fraction in trace results
local DRAG_COEFFICIENT = 0.029374 -- Combined drag coefficients for drag simulation

-- Helper function to normalize angles
local function normalize_angle(angle)
   if angle > 180 then
      angle = angle - 360
   elseif angle < -180 then
      angle = angle + 360
   end
   return angle
end

---@param player Entity
---@return StrafeResult?
local function CalcStrafe(player)
   local strafes = nil
   local index = player:GetIndex()
   local velocity = player:EstimateAbsVelocity() or Vector3()
   local currentPos = player:GetAbsOrigin()

   --- target not moving, dont do anything and just return nil
   if velocity and velocity:Length2D() < 1 then
      return {
         --- yeah doez nothing
         currentPos = currentPos,
         predictedPos = currentPos,
         strafeCenter = 0,
         deltaAngle = 0,
         moving = false,
      }
   end

   local velocityAngle = velocity:Angles()

   -- Initialize the history if needed
   strafeAngleHistories[index] = strafeAngleHistories[index] or {}
   centerHistories[index] = centerHistories[index] or {}

   -- Calculate delta velocity angle
   local previousAngle = strafeAngleHistories[index][#strafeAngleHistories[index]] or velocityAngle.y
   local delta = velocityAngle.y - previousAngle

   -- Normalize the angle between -180 and 180 degrees
   delta = normalize_angle(delta)

   -- Update angle history
   tableInsert(strafeAngleHistories[index], velocityAngle.y)
   if #strafeAngleHistories[index] > MAX_ANGLE_HISTORY then
      tableRemove(strafeAngleHistories[index], 1)
   end

   local tickinterval = TickInterval()

   if #strafeAngleHistories[index] >= 3 then
      local center = velocityAngle.y
      tableInsert(centerHistories[index], center)

      if #centerHistories[index] > MAX_CENTER_HISTORY then
         tableRemove(centerHistories[index], 1)
      end

      local mostRecentCenter = centerHistories[index][#centerHistories[index]]

      local predictedPos = Vector3(
         currentPos.x + (velocity.x * tickinterval),
         currentPos.y + (velocity.y * tickinterval),
         currentPos.z + (velocity.z * tickinterval)
      )

      strafes = {
         currentPos = currentPos,
         predictedPos = predictedPos,
         strafeCenter = mostRecentCenter,
         deltaAngle = delta,
         moving = true,
      }
   end

   return strafes
end

-- Normalize vector function
---@param Vector Vector3
local function Normalize(Vector)
   return Vector / Vector:Length()
end

-- Rotate vector function
local function RotateVector(vector, angle)
   local rad = math_rad(angle)
   local cosAngle = math_cos(rad)
   local sinAngle = math_sin(rad)
   return Vector3(
      vector.x * cosAngle - vector.y * sinAngle,
      vector.x * sinAngle + vector.y * cosAngle,
      vector.z
   )
end

-- Helper function for forward collision
---@param vel Vector3
---@param wallTrace Trace
local function handleForwardCollision(vel, wallTrace)
   local normal = wallTrace.plane
   --local angle = math_deg(math_acos(normal:Dot(vUp)))
   local dot = normal:Dot(vUp) -- still testing if all this math is worth it, although im certain it is way more expensive
   local angle = math_deg(math_acos(math_min(1, math_max(-1, dot / (normal:Length() * vUp:Length())))))
   if angle > FORWARD_COLLISION_ANGLE then
      local dot = vel:Dot(normal)
      vel = vel - normal * (dot * 2)
   end
   return wallTrace.endpos.x, wallTrace.endpos.y
end

-- Helper function for ground collision
---@param vel Vector3
---@param groundTrace Trace
local function handleGroundCollision(vel, groundTrace)
   local normal = groundTrace.plane
   local angle = math_deg(math_acos(normal:Dot(vUp)))
   local onGround = false
   if angle < GROUND_COLLISION_ANGLE_LOW then
      onGround = true
   elseif angle < GROUND_COLLISION_ANGLE_HIGH then
      vel.x, vel.y, vel.z = 0, 0, 0
   else
      local dot = vel:Dot(normal)
      vel = vel - normal * (dot * 2)
      onGround = true
   end
   if onGround then vel.z = 0 end
   return groundTrace.endpos, onGround
end

local function calculateHitChancePercentage(lastPredictedPos, currentPos)
   if not lastPredictedPos then
      print("lastPosition is NIL ~~!!!!")
      return 0
   end

   -- Calculate horizontal distance (2D distance on the X-Y plane)
   local horizontalDistance = math_sqrt((currentPos.x - lastPredictedPos.x) ^ 2 +
      (currentPos.y - lastPredictedPos.y) ^
      2)

   -- Calculate vertical distance with an allowance for vertical movement
   local verticalDistance = math_abs(currentPos.z - lastPredictedPos.z)

   -- Define maximum acceptable distances
   local maxHorizontalDistance = 12 -- Max acceptable horizontal distance in units
   local maxVerticalDistance = 45   -- Max acceptable vertical distance in units

   -- Normalize the distances to a 0-1 scale
   local horizontalFactor = math_min(horizontalDistance / maxHorizontalDistance, 1)
   local verticalFactor = math_min(verticalDistance / maxVerticalDistance, 1)

   -- Calculate the hit chance as a percentage
   local overallFactor = (horizontalFactor + verticalFactor) / 2

   -- Convert to a percentage where 100% is perfect and 0% is a miss
   local hitChancePercentage = (1 - overallFactor) * 100

   return hitChancePercentage
end

-- Optimized path clearance check
local function checkPathClearance(dest, direction, angle, distance, origin, targetIndex)
   -- Pre-calculate points and vectors once
   local rotatedVector = RotateVector(direction, angle) * distance
   local point = dest + rotatedVector

   local function shouldHitEntity(entity)
      return entity:GetIndex() ~= targetIndex
   end

   local traceDown = TraceLine(
      point,
      point + Vector3(0, 0, -100),
      (MASK_SHOT_HULL | CONTENTS_GRATE),
      shouldHitEntity
   )

   local endPos = traceDown.endpos
   local toDestVector = endPos - dest
   local distanceToTarget = toDestVector:Length()

   if distanceToTarget > distance then
      local excessDistance = distanceToTarget - distance
      endPos = endPos + (vector.Normalize(toDestVector) * excessDistance)
   end

   local visibilityCheck = TraceLine(origin, dest, MASK_SHOT_HULL, shouldHitEntity)

   return visibilityCheck.fraction <= 0.8, endPos
end

-- Simplified path check
local function checkPath(origin, dest, targetIndex, direction, angle, distance)
   local point = dest + RotateVector(direction, angle) * distance

   local trace = TraceLine(origin, point, (MASK_SHOT_HULL), function(entity) return entity:GetIndex() ~= targetIndex end)

   return trace.fraction > 0.9, trace.endpos
end

-- Optimized best shooting position finder
local function FindBestShootingPosition(origin, dest, target, BlastRadius)
   local targetIndex = target:GetIndex()

   -- Initial visibility check
   local initialTrace = TraceLine(origin, dest, MASK_PLAYERSOLID,
      function(entity) return entity:GetIndex() ~= targetIndex end)

   -- Early return if direct path is clear
   if initialTrace.fraction >= 1 or initialTrace.entity:GetIndex() == targetIndex then
      return dest
   end

   local direction = Normalize(dest - origin)

   local leftClear, leftPoint = checkPathClearance(dest, direction, -90, BlastRadius, origin, targetIndex)
   local rightClear, rightPoint = checkPathClearance(dest, direction, 90, BlastRadius, origin, targetIndex)

   local searchSide, maxPoint
   if leftClear and rightClear then
      local leftDist = (leftPoint - dest):LengthSqr()
      local rightDist = (rightPoint - dest):LengthSqr()

      if leftDist < rightDist then
         searchSide, maxPoint = -90, leftPoint
      else
         searchSide, maxPoint = 90, rightPoint
      end
   elseif leftClear then
      searchSide, maxPoint = -90, leftPoint
   elseif rightClear then
      searchSide, maxPoint = 90, rightPoint
   else
      return false
   end

   local minDistance = 0
   local maxDistance = (maxPoint - dest):Length()
   local iterations = Menu.Advanced.SplashAccuracy or 5
   local bestPoint = maxPoint
   local bestDistance = maxDistance

   for i = 1, iterations do
      local midDistance = (minDistance + maxDistance) * 0.5
      local isClear, midPoint = checkPath(origin, dest, targetIndex, direction, searchSide, midDistance)

      if isClear then
         local distToDest = (midPoint - dest):Length()
         if distToDest < bestDistance then
            bestDistance = distToDest
            bestPoint = midPoint
         end
         maxDistance = midDistance
      else
         minDistance = midDistance
      end
   end

   projectileSimulation2 = bestPoint
   return bestPoint
end
-- Function to solve projectile trajectory and return the necessary angles and time to hit a target
---@param origin Vector3  -- The starting position of the projectile
---@param dest Vector3  -- The destination or target position
---@param speed number  -- The initial speed of the projectile
---@param gravity number  -- The gravity factor affecting the projectile
---@param sv_gravity number  -- The server's gravity setting
---@param target Entity  -- The target entity to avoid hitting with the projectile
---@param timeToHit number  -- The maximum allowed time to hit the target
---@return { angles: EulerAngles, time: number, Prediction: Vector3, Positions: table, fov: number }|false?  -- Returns calculated angles, time, predicted final position, and the flight path positions
local function SolveProjectile(origin, dest, speed, gravity, sv_gravity, target, timeToHit)
   -- validate input vectors first
   if not validateVector(origin) or not validateVector(dest) then
      return false
   end

   local function calculateStraight()
      local direction = dest - origin
      local time_to_target = direction:Length() / speed

      if time_to_target > timeToHit then
         return false
      end

      local trace = TraceLine(origin, dest, MASK_PLAYERSOLID)

      if not validateVector(trace.endpos) then
         return false
      end

      if trace.fraction ~= FULL_HIT_FRACTION and trace.entity:GetName() ~= target:GetName() then
         return false
      end

      projectileSimulation = { origin, trace.endpos }
      local angles = ngl.CalcAngle(origin, dest)
      if not angles then return nil end
      local fov = ngl.CalcFov(angles, engine:GetViewAngles())
      if not fov then return nil end
      --if isNaN(angles.x) or isNaN(angles.y) or isNaN(angles.z) then return nil end
      if not validateVector(Vector3(angles:Unpack())) or isNaN(fov) then return nil end
      --print(string.format("origin: %s | dest: %s | angles: %s\nspeed: %s | target: %s", tostring(origin), tostring(dest),
      --tostring(angles), tostring(speed), tostring(target:GetName())))
      return {
         angles = angles,
         fov = fov,
         time = time_to_target,
         Prediction = dest,
         Positions = { origin, dest }
      }
   end

   local function calculateBallistic(effective_gravity)
      -- Calculate the direction vector from origin to destination
      local direction = dest - origin

      -- Calculate squared speed for later use in equations
      local speed_squared = speed * speed

      -- Calculate the effective gravity based on server gravity settings and the specified gravity factor

      -- Calculate the horizontal (2D) distance and vertical (Z-axis) distance between origin and destination
      local horizontal_distance = direction:Length2D()
      local vertical_distance = direction.z
      -- Ballistic arc calculation when gravity is present

      -- Calculate the term related to gravity and horizontal distance squared
      local gravity_horizontal_squared = effective_gravity * horizontal_distance * horizontal_distance

      -- Solve the quadratic equation for projectile motion
      local discriminant = speed_squared * speed_squared -
          effective_gravity * (gravity_horizontal_squared + 2 * vertical_distance * speed_squared)
      if discriminant < 0 then return nil end -- No real solution, so return nil

      -- Calculate the pitch and yaw angles required for the projectile to reach the target
      local sqrt_discriminant = math_sqrt(discriminant)
      local pitch_angle = math_atan((speed_squared - sqrt_discriminant) / (effective_gravity * horizontal_distance))
      local yaw_angle = math_atan(direction.y, direction.x)

      if isNaN(pitch_angle) or isNaN(yaw_angle) then return nil end

      -- Convert the pitch and yaw into Euler angles
      local calculated_angles = EulerAngles(pitch_angle * -M_RADPI, yaw_angle * M_RADPI)
      local fov = ngl.CalcFov(calculated_angles, engine:GetViewAngles())

      -- Calculate the time it takes for the projectile to reach the target
      local time_to_target = horizontal_distance / (math_cos(pitch_angle) * speed)

      if time_to_target > timeToHit then
         return false -- Projectile will fly out of range, so return false
      end

      -- Define the number of segments to divide the trajectory into for simulation (default is 2)
      local number_of_segments = math_max(1, Menu.Advanced.ProjectileSegments or 2)
      local segment_duration = time_to_target / number_of_segments
      local current_position = origin
      local current_velocity = speed

      -- Table to store positions along the projectile's path
      projectileSimulation = { current_position }

      -- Simulate the projectile's flight path
      for segment = 1, number_of_segments do
         local time_segment = segment * segment_duration

         -- Apply drag to the current velocity over time
         current_velocity = current_velocity * math_exp(-DRAG_COEFFICIENT * time_segment)

         -- Calculate the new position based on current velocity, pitch, yaw, and gravity
         local horizontal_displacement = current_velocity * math_cos(pitch_angle) * time_segment
         local vertical_displacement = current_velocity * math_sin(pitch_angle) * time_segment -
             0.5 * effective_gravity * time_segment * time_segment
         local new_position = origin +
             Vector3(horizontal_displacement * math_cos(yaw_angle), horizontal_displacement * math_sin(yaw_angle),
                vertical_displacement)

         -- Perform a trace to check for collisions
         local trace = TraceLine(current_position, new_position, MASK_PLAYERSOLID)

         -- Save the new position to the projectile path
         tableInsert(projectileSimulation, new_position)

         -- Check if the projectile collided with something that isn't the target
         if trace.fraction < FULL_HIT_FRACTION and trace.entity ~= target then
            return false -- Collision detected, exit the loop
         end

         -- Update the current position for the next segment
         current_position = new_position
      end

      -- Return the calculated angles, time to target, final predicted position, and all positions along the path
      return {
         angles = calculated_angles,
         fov = fov,
         time = time_to_target,
         Prediction = current_position,
         Positions = projectileSimulation
      }
   end

   local effective_gravity = sv_gravity * gravity
   if effective_gravity == 0 then
      return calculateStraight()
   else
      return calculateBallistic(effective_gravity)
   end
end

-- Function to calculate the trust factor based on the number of records
local function calculateTrustFactor(numRecords, maxRecords, growthRate)
   -- Ensure we avoid division by zero
   if maxRecords == 0 then
      return 0
   end

   -- Calculate the ratio of current records to maximum records
   local ratio = numRecords / maxRecords

   -- Apply a logarithmic function to grow the trust factor
   local trustFactor = math.log(1 + ratio * (math.exp(growthRate) - 1)) / growthRate

   -- Ensure the trust factor is capped at 1
   if trustFactor > 1 then
      trustFactor = 1
   end

   -- Round the trust factor to 2 decimal places
   trustFactor = math_floor((trustFactor * 100) + 0.5) / 100

   return trustFactor
end

-- Function to calculate the adjusted hit chance
local function calculateAdjustedHitChance(hitChance, trustFactor)
   -- Apply the trust factor as a multiplier to the hit chance
   return math_floor((hitChance * trustFactor * 100) + 0.5) / 100
end

local function GetBonePosition(entity, hitbox)
   local model = entity:GetModel()
   local studioHdr = models.GetStudioModel(model)

   local myHitBoxSet = entity:GetPropInt("m_nHitboxSet")
   local hitboxSet = studioHdr:GetHitboxSet(myHitBoxSet)
   local hitboxes = hitboxSet:GetHitboxes()
   local hitbox = hitboxes[hitbox]

   local boneMatrices = entity:SetupBones()
   local bone = hitbox:GetBone()
   local boneMatrix = boneMatrices[bone]

   if boneMatrix == nil then return nil end
   local bonePos = Vector3(boneMatrix[1][4], boneMatrix[2][4], boneMatrix[3][4])
   return bonePos
end

---@param player Entity
local function GetBodyPosition(player)
   return GetBonePosition(player, Hitbox.Pelvis)
end

local function GetHeadPosition(player)
   return GetBonePosition(player, Hitbox.Head)
end

--- i wish there was a better way to do this, but i cant think of one for now
local function GetFeetPosition(player)
   return player:GetAbsOrigin() + Vector3(0, 0, 10)
end

---@param weapon Entity
---@param player Entity
local function GetAimPos(weapon, player)
   --local aimPos = weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ROCKET and GetFeetPosition(player) or weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ARROW and GetHeadPosition(player) or GetBodyPosition(player)
   if weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ROCKET
       or weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_PIPEBOMB then
      return GetFeetPosition(player)
   elseif weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ARROW then
      local class = player:GetPropInt("m_PlayerClass", "m_iClass")
      --- player is a medic or sniper?
      if class == 2 then     --- medic
         return GetBodyPosition(player)
      elseif class == 5 then --- sniper
         return GetHeadPosition(player)
      end
   else
      return GetBodyPosition(player)
   end
end

---@param me Entity
---@param weapon Entity
---@param player Entity
---@param building boolean
---@return AimTarget?
local function CheckProjectileTarget(me, weapon, player, building)
   local aimPos = GetAimPos(weapon, player)
   if not aimPos then return nil end

   local tick_interval = TickInterval()
   local shootPos = ngl.GetShootPos(me)
   local meOrigin = me:GetAbsOrigin()
   local playerOrigin = player:GetAbsOrigin()
   local playerIndex = player:GetIndex()
   local flags = player:GetPropInt("m_fFlags")
   local stepSize = player:GetPropFloat("localdata", "m_flStepSize") or 18
   local vStep = Vector3(0, 0, stepSize / 2)

   local aimOffset = aimPos - player:GetAbsOrigin()
   local gravity = GetConVar("sv_gravity")

   ---@type StrafeResult?
   local strafeAngle = Menu.Advanced.StrafePrediction and strafeAngles[playerIndex] or nil

   vPath = {}
   local lastP, lastV, lastG = player:GetAbsOrigin(), player:EstimateAbsVelocity(),
       (flags and flags & FL_ONGROUND ~= 0) or (player:GetClass() ~= "CTFPlayer" and building)
   local BlastRadius = 150

   -- trace ignore simulated player
   local function shouldHitEntity(entity)
      return entity:GetIndex() ~= playerIndex or
          entity:GetTeamNumber() ~= player:GetTeamNumber()
   end

   -- Check initial conditions
   local projInfo = ngl.GetProjectileInfo(weapon)
   if not projInfo or not gravity or not stepSize then return nil end

   local PredTicks = Menu.Advanced.PredTicks

   local speed = projInfo[1]
   if vectorDistance(aimPos, playerOrigin) > PredTicks * speed then return nil end

   local targetAngles, fov
   local lastAppliedAngle = 0
   local targetAngle = 0
   -- Initialize storage for predictions if not already initialized
   if not lastPosition[playerIndex] then lastPosition[playerIndex] = {} end
   if not priorPrediction[playerIndex] then priorPrediction[playerIndex] = {} end
   if not hitChanceRecords[playerIndex] then hitChanceRecords[playerIndex] = {} end

   -- Variables to accumulate hit chances
   local totalHitChance = 0
   local tickCount = 0

   -- main loop for prediction and projectile calculations
   for i = 1, PredTicks * 2 do
      local pos = lastP + lastV * tick_interval
      local vel = lastV
      local onGround = lastG

      -- Apply strafeAngle with smoothing
      if strafeAngle and strafeAngle.deltaAngle and strafeAngle.strafeCenter and strafeAngle.predictedPos then
         local currentDir = Normalize(Vector3(vel.x, vel.y, 0))

         -- Calculate distance to predicted position
         local distanceToTarget = (strafeAngle.predictedPos - player:GetAbsOrigin()):Length2D()

         -- Distance-based smoothing factors
         local distanceMultiplier = math.min(1.0, 400 / math.max(distanceToTarget, 1))
         local baseSmoothFactor = 1
         local smoothFactor = baseSmoothFactor * distanceMultiplier

         -- Calculate strafe intensity with distance consideration
         local baseIntensity = math.min(Normalize(vel):Length2D() * 0.8, 1.0)
         local strafeIntensity = baseIntensity * (0.7 + (distanceMultiplier * 0.3))

         -- Smoothly interpolate the target angle with distance-aware lerp
         targetAngle = strafeAngle.deltaAngle * strafeIntensity
         local baseLerpFactor = 0.15
         local lerpFactor = baseLerpFactor * distanceMultiplier

         -- Add extra angle dampening at distance
         if distanceToTarget > 500 then
            local dampening = math.max(0.4, 1.0 - ((distanceToTarget - 500) / 1000))
            targetAngle = targetAngle * dampening
         end

         -- Interpolate between current and target angle
         lastAppliedAngle = lastAppliedAngle + (targetAngle - lastAppliedAngle) * lerpFactor
         local appliedAngle = lastAppliedAngle * smoothFactor

         -- Convert to radians for rotation
         local rotationRad = math_rad(appliedAngle)

         -- Rotate the velocity vector
         local rotatedX = currentDir.x * math_cos(rotationRad) - currentDir.y * math_sin(rotationRad)
         local rotatedY = currentDir.x * math_sin(rotationRad) + currentDir.y * math_cos(rotationRad)

         -- Apply the rotated direction while maintaining speed
         local speed = vel:Length2D()

         -- Add slight speed dampening during sharp turns, reduced at distance
         local turnSharpness = math.abs(appliedAngle) / 90
         local speedMultiplier = math.max(1 - (turnSharpness * 0.2 * distanceMultiplier), 0.85)

         vel.x = rotatedX * speed * speedMultiplier
         vel.y = rotatedY * speed * speedMultiplier

         -- Consider strafe center tendency with distance-aware smoothing
         if strafeAngle.strafeCenter then
            local centerDiff = normalize_angle(strafeAngle.strafeCenter - math_deg(math_atan(vel.y, vel.x)))
            local centerInfluence = math.min(math.abs(centerDiff) / 90, 1.0) * distanceMultiplier

            if math.abs(centerDiff) > 45 then
               local reductionFactor = 0.99 + (centerInfluence * 0.01)
               vel = vel * reductionFactor
            end
         end
      end

      -- Forward Collision
      local wallTrace = TraceHull(lastP + vStep, pos + vStep, vHitbox[1], vHitbox[2], MASK_PLAYERSOLID,
         shouldHitEntity)
      if wallTrace.fraction < 1 then
         pos.x, pos.y = handleForwardCollision(vel, wallTrace)
      end

      -- Ground Collision
      local downStep = onGround and vStep or Vector3()
      local groundTrace = TraceHull(pos + vStep, pos - downStep, vHitbox[1], vHitbox[2], MASK_PLAYERSOLID,
         shouldHitEntity)
      if groundTrace.fraction < 1 then
         pos, onGround = handleGroundCollision(vel, groundTrace)
      else
         onGround = false
      end

      -- Apply gravity if not on ground
      if not onGround then
         vel.z = vel.z - gravity * tick_interval
      end

      --- 1 day trying to fix this shit, to just having to reset it to fix. I want to die
      if not validateVector(vel) then vel = Vector3() end

      lastP, lastV, lastG = pos, vel, onGround

      -- Projectile Targeting Logic
      pos = lastP + aimOffset + Vector3(0, 0, vel.z * tick_interval)
      vPath[i] = pos -- save path for visuals

      -- Hitchance check and synchronization of predictions
      if i <= PredTicks then
         local currentTick = PredTicks - i -- Determine which tick in the future we're currently predicting

         -- Store the last prediction of the current tick
         lastPosition[playerIndex][currentTick] = priorPrediction[playerIndex][currentTick] or pos

         -- Update priorPrediction with the current predicted position for this tick
         priorPrediction[playerIndex][currentTick] = pos

         -- Calculate hit chance for the current tick
         local hitChance1 = calculateHitChancePercentage(lastPosition[playerIndex][currentTick],
            priorPrediction[playerIndex][currentTick])

         -- Insert the hit chance record
         tableInsert(hitChanceRecords[playerIndex], hitChance1)

         -- Ensure the number of records does not exceed the maximum allowed
         local maxRecords = Menu.Advanced.Hitchance_Accuracy
         if #hitChanceRecords[playerIndex] > maxRecords then
            tableRemove(hitChanceRecords[playerIndex], 1) -- Remove the oldest record
         end

         -- Accumulate hit chance and tick count
         totalHitChance = totalHitChance + hitChance1
         tickCount = tickCount + 1
      end

      -- Solve the projectile based on the current position
      local solution = SolveProjectile(shootPos, pos, projInfo[1], projInfo[2], gravity, player,
         PredTicks * tick_interval)
      if solution == nil then goto continue end

      if not solution then
         if Menu.Advanced.SplashPrediction and projInfo[2] == 0 then
            local bestPos = FindBestShootingPosition(shootPos, pos, player, BlastRadius)
            if bestPos then
               solution = SolveProjectile(shootPos, bestPos, projInfo[1], projInfo[2], gravity, player,
                  PredTicks * tick_interval)
            end
         else
            return nil
         end
      end

      local time
      if solution and solution.time then
         time = solution.time + latency + lerp
      else
         return nil
      end

      --- Time to tick
      local ticks = (time * 66.67) + 1
      if ticks > i then goto continue end

      targetAngles = solution.angles
      break
      ::continue::
   end

   -- calculate the average hit chance and set the global hitChance variable
   if tickCount > 0 then
      hitChance = totalHitChance / tickCount
   else
      hitChance = 0
   end

   -- calculate trust factor based on the number of records
   local numRecords = #hitChanceRecords[playerIndex]
   local growthRate = Menu.Advanced.AccuracyWeight or 1
   local trustFactor = calculateTrustFactor(numRecords, Menu.Advanced.Hitchance_Accuracy, growthRate)

   -- Adjust the average hit chance based on trust factor
   hitChance = calculateAdjustedHitChance(hitChance, trustFactor)

   -- check if the average adjusted hit chance meets the minimum required threshold
   if hitChance < Menu.Main.MinHitchance then
      return nil -- If not, return nil to indicate that the prediction is not reliable
   end

   if not targetAngles or (playerOrigin - meOrigin):Length() < 100 or not lastPosition[playerIndex] then
      return nil
   end

   return { entity = player, angles = targetAngles, factor = nil, Prediction = vPath[#vPath] }
end

---@param name string
local function bGetGUIValue(name)
   return gui.GetValue(name) == 1
end

---@param me Entity
---@param players table<integer, Entity>
---@param bestTarget Entity?
---@param bestFactor number?
local function GetBestPlayer(me, players, bestTarget, bestFactor)
   local myteamnumber = me:GetTeamNumber()
   local localPlayerOrigin = me:GetAbsOrigin()
   local localPlayerViewAngles = engine.GetViewAngles()
   local aimfov = gui.GetValue("aim fov")
   for _, player in pairs(players) do
      if player:GetTeamNumber() == myteamnumber then goto continue end
      if player:IsDormant() or not player:IsAlive() then goto continue end
      if player:InCond(E_TFCOND.TFCond_Ubercharged) then goto continue end -- we have no ignore ubercharge on lbox menu soo yeah we just ignore them
      if player:InCond(E_TFCOND.TFCond_Cloaked) and bGetGUIValue("ignore cloaked") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Taunting) and bGetGUIValue("ignore taunting") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Disguised) and bGetGUIValue("ignore disguised") then goto continue end
      if player:InCond(E_TFCOND.TFCond_DeadRingered) and bGetGUIValue("ignore deadringer") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Bonked) and bGetGUIValue("ignore bonked") then goto continue end
      if bGetGUIValue("ignore steam friends") and playerlist.GetPriority(player) == -1 then goto continue end -- if priority = friend then skip :3

      local scan = ngl.ScanBody(me, player)
      if not scan then
         if not scan then goto continue end
      end

      local fov = ngl.CalcFov(scan.angle, localPlayerViewAngles)
      if fov > aimfov then
         goto continue
      end

      --local mecenter, targetcenter = ngl.GetEntityCenter(me), ngl.GetEntityCenter(player)

      local plrOrigin = scan.pos
      ---@diagnostic disable-next-line: need-check-nil
      local distance = math_abs(plrOrigin.x - localPlayerOrigin.x) +
          ---@diagnostic disable-next-line: need-check-nil
          math_abs(plrOrigin.y - localPlayerOrigin.y) +
          ---@diagnostic disable-next-line: need-check-nil
          math_abs(plrOrigin.z - localPlayerOrigin.z)

      local distanceFactor = ngl.RemapValClamped(distance, 50, 2500, 1, 0.09)
      local fovFactor = ngl.RemapValClamped(fov, 0, aimfov, 1, 0.7)
      local visibilityFactor = scan.angle and 1 or 0.5 -- visibility factor is useless, we already check
      local factor = fovFactor * distanceFactor * visibilityFactor

      if factor > bestFactor then
         bestTarget = player
         bestFactor = factor
      end

      ::continue::
   end

   return bestTarget, bestFactor
end

local function GetBestBuilding(me, buildings, bestTarget, bestFactor)
   local myteamnumber = me:GetTeamNumber()
   local localPlayerOrigin = ngl.GetShootPos(me)
   local localPlayerViewAngles = engine.GetViewAngles()
   local aimfov = gui.GetValue("aim fov")
   for _, building in pairs(buildings) do
      if building:IsDormant() or building:GetHealth() == 0 or building:GetTeamNumber() == myteamnumber then goto continue end
      local buildingOrigin = ngl.GetEntityCenter(building)

      local isVisible = ngl.VisPos(building, localPlayerOrigin, buildingOrigin)
      --- if not visible just skip
      if not isVisible then
         goto continue
      end

      local angles = ngl.CalcAngle(localPlayerOrigin, buildingOrigin)
      local fov = ngl.CalcFov(angles, localPlayerViewAngles)

      if fov > aimfov then
         goto continue
      end

      local distance = math_abs(buildingOrigin.x - localPlayerOrigin.x) +
          math_abs(buildingOrigin.y - localPlayerOrigin.y) +
          math_abs(buildingOrigin.z - localPlayerOrigin.z)

      local distanceFactor = ngl.RemapValClamped(distance, 50, 2500, 1, 0.09)
      local fovFactor = ngl.RemapValClamped(fov, 0, aimfov, 1, 0.7)
      local visibilityFactor = isVisible and 1 or 0.5
      local factor = fovFactor * visibilityFactor * distanceFactor

      if factor > bestFactor then
         bestTarget = building
         bestFactor = factor
      end
      ::continue::
   end

   return bestTarget, bestFactor
end

---@param me Entity
---@param weapon Entity
local function GetBestTarget(me, weapon)
   local players = FindByClass("CTFPlayer")

   local bestTarget = nil
   local bestFactor = 0

   if bGetGUIValue("aim other buildings") then
      local teleporters = FindByClass("CObjectDispenser")
      local dispensers = FindByClass("CObjectTeleporter")
      bestTarget, bestFactor = GetBestBuilding(me, dispensers, bestTarget, bestFactor)
      bestTarget, bestFactor = GetBestBuilding(me, teleporters, bestTarget, bestFactor)
   end

   --- sentries will have the most priority, for obvious reasons (most risk for life)
   if bGetGUIValue("aim sentry") then
      local sentries = FindByClass("CObjectSentrygun")
      bestTarget, bestFactor = GetBestBuilding(me, sentries, bestTarget, bestFactor)
   end

   bestTarget, bestFactor = GetBestPlayer(me, players, bestTarget, bestFactor)

   if bestTarget then
      local class = bestTarget:GetClass()

      local building = class == "CObjectSentrygun" or class == "CObjectDispenser" or class == "CObjectTeleporter"

      return CheckProjectileTarget(me, weapon, bestTarget, building)
   else
      return nil
   end
end

local function CreateMove_PredictInBackground(usercmd)
   --- check if aimbot is enabled on lbox
   if gui.GetValue("aim bot") == 1 then return end
   if engine.IsChatOpen() or engine.Con_IsVisible() or engine.IsGameUIVisible() then return end

   local me = entities:GetLocalPlayer()
   if not me or not me:IsAlive() then return end

   local weapon = ngl.GetCurrentWeapon(me)
   if not weapon then return end

   local isHitscan = weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_BULLET
   local isMelee = weapon:IsMeleeWeapon()

   -- Calculate strafe angles (optional)
   if currentTarget and Menu.Advanced.StrafePrediction and not isHitscan and not isMelee then
      local strafe = CalcStrafe(currentTarget.entity)
      if strafe and currentTarget and currentTarget.entity and strafe.moving then
         strafeAngles[currentTarget.entity:GetIndex()] = strafe
      end
   end
end

local function AutoShoot(userCmd, weapon)
   if weapon:GetWeaponID() == TF_WEAPON_COMPOUND_BOW or weapon:GetWeaponID() == TF_WEAPON_PIPEBOMBLAUNCHER then
      -- Huntsman
      if weapon:GetChargeBeginTime() > 0 then
         userCmd.buttons = userCmd.buttons & ~IN_ATTACK
      else
         userCmd.buttons = userCmd.buttons | IN_ATTACK
      end
   else
      -- Normal weapon
      userCmd.buttons = userCmd.buttons | IN_ATTACK
   end
end

---@param userCmd UserCmd
local function OnCreateMove(userCmd)
   --- check if aimbot is enabled on lbox
   local me = entities:GetLocalPlayer()
   if not me or not me:IsAlive() then return end

   local weapon = ngl.GetCurrentWeapon(me)
   if not weapon then return end

   local isHitscan = weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_BULLET
   local isMelee = weapon:IsMeleeWeapon()

   gui.SetValue("aim bot", (isHitscan or isMelee) and 1 or 0)

   if isMelee then return end

   if engine.IsChatOpen() or engine.Con_IsVisible() or engine.IsGameUIVisible() then return end
   if not input.IsButtonDown(gui.GetValue("aim key")) then
      return
   end

   local canshoot = ngl.CanWeaponShoot(me, weapon)
   if not canshoot then return end

   local netchannel = clientstate.GetNetChannel()
   if not netchannel then return end

   -- Get current latency
   local latIn, latOut = netchannel:GetLatency(E_Flows.FLOW_INCOMING), netchannel:GetLatency(E_Flows.FLOW_OUTGOING)
   latency = (latIn or 0) + (latOut or 0)

   -- Get current lerp
   lerp = GetConVar("cl_interp") or 0

   collectgarbage("stop")

   -- Get the best target
   currentTarget = GetBestTarget(me, weapon)
   collectgarbage("restart")

   if currentTarget == nil or currentTarget.angles == nil then
      return
   end

   if currentTarget and Menu.Main.triggerbot == true then
      local fov = ngl.CalcFov(engine:GetViewAngles(), currentTarget.angles)
      if fov <= 3 then
         AutoShoot(userCmd, weapon)
      end

      goto skipstuff
   end

   -- Auto Shoot
   if bGetGUIValue("auto shoot") then
      AutoShoot(userCmd, weapon)
   end

   if (userCmd.buttons & IN_ATTACK ~= 0) and currentTarget and currentTarget.angles then
      local projMethod = gui.GetValue("aim method (projectile)")

      -- Aim at the target
      userCmd:SetViewAngles(currentTarget.angles:Unpack())
      userCmd:SetSendPacket(not (projMethod == "silent +" and not isHitscan))

      if (projMethod == "plain" or projMethod == "smooth") then
         engine.SetViewAngles(EulerAngles(currentTarget.angles:Unpack()))
      end

      return
   end

   ::skipstuff::
end

local font = draw.CreateFont("Verdana", 12, 400, FONTFLAG_OUTLINE)
draw.SetFont(font)

local function L_line(start_pos, end_pos, secondary_line_size)
   if not (start_pos and end_pos) then
      return
   end
   local direction = end_pos - start_pos
   local direction_length = direction:Length()
   if direction_length == 0 then
      return
   end
   local normalized_direction = Normalize(direction)
   local perpendicular = Vector3(normalized_direction.y, -normalized_direction.x, 0) * secondary_line_size
   local w2s_start_pos = WorldToScreen(start_pos)
   local w2s_end_pos = WorldToScreen(end_pos)
   if not (w2s_start_pos and w2s_end_pos) then
      return
   end
   local secondary_line_end_pos = start_pos + perpendicular
   local w2s_secondary_line_end_pos = WorldToScreen(secondary_line_end_pos)
   if w2s_secondary_line_end_pos then
      draw_Line(w2s_start_pos[1], w2s_start_pos[2], w2s_end_pos[1], w2s_end_pos[2])
      draw_Line(w2s_start_pos[1], w2s_start_pos[2], w2s_secondary_line_end_pos[1], w2s_secondary_line_end_pos[2])
   end
end

local hitPos = {}
local function PlayerHurtEvent(event)
   if (event:GetName() == 'player_hurt') and Menu.Visuals.VisualizeHitPos then
      local localPlayer = entities.GetLocalPlayer();
      if not localPlayer then return end
      local victim = entities.GetByUserID(event:GetInt("userid"))
      if not victim then return end
      local attacker = entities.GetByUserID(event:GetInt("attacker"))
      if (attacker == nil or localPlayer:GetIndex() ~= attacker:GetIndex()) then
         return
      end
      tableInsert(hitPos, 1, { box = victim:HitboxSurroundingBox(), time = globals.RealTime() })
   end
   if #hitPos > 1 then
      tableRemove(hitPos)
   end
end
callbacks.Register("FireGameEvent", "PlayerHurtEvent", PlayerHurtEvent)

local clear_lines = 0

local function OnDraw()
   draw.SetFont(font)
   draw.Color(255, 255, 255, 255)
   local aimKeyDown = input.IsButtonDown(gui.GetValue("aim key"))
   if not aimKeyDown then
      if (globals.RealTime() > (clear_lines + 5)) then
         vPath = {}
         clear_lines = globals.RealTime()
      end
   else
      clear_lines = globals.RealTime()
   end
   -- Draw lines between the predicted positions
   --if Menu.Visuals.Active and vPath then
   local mode = string.lower(gui.GetValue("projectile aimbot"))
   if (mode == "draw") and vPath then
      local startPos
      draw.SetFont(font)
      for i = 1, #vPath - 1 do
         local pos1 = vPath[i]
         local pos2 = vPath[i + 1]

         if i == 1 then
            startPos = pos1
         end

         --draw.Color(255 - math_floor((hitChance / 100) * 255), math_floor((hitChance / 100) * 255), 0, 255)
         draw.Color(255, 255, 255, 150)

         --draw predicted local position with strafe prediction
         if projectileSimulation2 and projectileSimulation2 ~= EMPTY_VECTOR then
            local screenPos = WorldToScreen(projectileSimulation2)
            if screenPos ~= nil then
               draw_Line(screenPos[1] + 10, screenPos[2], screenPos[1] - 10, screenPos[2])
               draw_Line(screenPos[1], screenPos[2] - 10, screenPos[1], screenPos[2] + 10)
            end
         end

         if Menu.Visuals.VisualizeHitchance or Menu.Visuals.Crosshair or Menu.Visuals.NccPred then
            if i == #vPath - 1 then
               local screenPos1 = WorldToScreen(pos1)
               local screenPos2 = WorldToScreen(pos2)

               if screenPos1 ~= nil and screenPos2 ~= nil then
                  if Menu.Visuals.VisualizeHitchance then
                     ---@diagnostic disable-next-line: param-type-mismatch
                     local width = draw.GetTextSize(math_floor(hitChance))
                     ---@diagnostic disable-next-line: param-type-mismatch
                     draw_Text(screenPos2[1] - math_floor(width / 2), screenPos2[2] + 20, math_floor(hitChance))
                  end
                  if Menu.Visuals.Crosshair then
                     local c_size = 8
                     draw_Line(screenPos2[1] - c_size, screenPos2[2], screenPos2[1] + c_size, screenPos2[2])
                     draw_Line(screenPos2[1], screenPos2[2] - c_size, screenPos2[1], screenPos2[2] + c_size)
                  end
                  if Menu.Visuals.NccPred then
                     local c_size = 5
                     draw_FilledRect(screenPos2[1] - c_size, screenPos2[2] - c_size, screenPos2[1] + c_size,
                        screenPos2[2] + c_size)
                     local w2s = WorldToScreen(startPos)
                     if w2s then
                        draw_Line(w2s[1], w2s[2], screenPos2[1], screenPos2[2])
                     end
                  end
               end
            end
         end

         if Menu.Visuals.VisualizePath then
            if Menu.Visuals.Path_styles_selected == 1 or Menu.Visuals.Path_styles_selected == 3 then
               local screenPos1 = WorldToScreen(pos1)
               local screenPos2 = WorldToScreen(pos2)

               if screenPos1 ~= nil and screenPos2 ~= nil and (not (Menu.Visuals.Path_styles_selected == 3) or i % 2 == 1) then
                  draw_Line(screenPos1[1], screenPos1[2], screenPos2[1], screenPos2[2])
               end
            end

            if Menu.Visuals.Path_styles_selected == 2 then
               L_line(pos1, pos2, 10)
            end

            if projectileSimulation and Menu.Visuals.VisualizeProjectile then
               for i = 1, #projectileSimulation - 1 do
                  local pos1 = projectileSimulation[i]
                  local pos2 = projectileSimulation[i + 1]

                  if pos1 and pos2 then
                     if Menu.Visuals.Path_styles_selected == 1 or Menu.Visuals.Path_styles_selected == 3 then
                        local screenPos1 = WorldToScreen(pos1)
                        local screenPos2 = WorldToScreen(pos2)

                        if screenPos1 ~= nil and screenPos2 ~= nil and (not (Menu.Visuals.Path_styles_selected == 3) or i % 2 == 1) then
                           draw_Line(screenPos1[1], screenPos1[2], screenPos2[1], screenPos2[2])
                        end
                     end
                     if Menu.Visuals.Path_styles_selected == 2 then
                        L_line(pos1, pos2, 10)
                     end
                  end
               end
            end
         end
      end

      if Menu.Visuals.VisualizeHitPos then
         for i, v in pairs(hitPos) do
            if globals.RealTime() - v.time > 1 then
               tableRemove(hitPos, i)
            else
               draw.Color(255, 255, 255, 255)
               local hitboxes = v.box
               local min = hitboxes[1]
               local max = hitboxes[2]
               local vertices = {
                  Vector3(min.x, min.y, min.z),
                  Vector3(min.x, max.y, min.z),
                  Vector3(max.x, max.y, min.z),
                  Vector3(max.x, min.y, min.z),
                  Vector3(min.x, min.y, max.z),
                  Vector3(min.x, max.y, max.z),
                  Vector3(max.x, max.y, max.z),
                  Vector3(max.x, min.y, max.z)
               }
               local screenVertices = {}
               for j, vertex in ipairs(vertices) do
                  local screenPos = WorldToScreen(vertex)
                  if screenPos ~= nil then
                     screenVertices[j] = { x = screenPos[1], y = screenPos[2] }
                  end
               end
               for j = 1, 4 do
                  local vertex1 = screenVertices[j]
                  local vertex2 = screenVertices[j % 4 + 1]
                  local vertex3 = screenVertices[j + 4]
                  local vertex4 = screenVertices[(j + 4) % 4 + 5]
                  if vertex1 ~= nil and vertex2 ~= nil and vertex3 ~= nil and vertex4 ~= nil then
                     draw_Line(vertex1.x, vertex1.y, vertex2.x, vertex2.y)
                     draw_Line(vertex3.x, vertex3.y, vertex4.x, vertex4.y)
                  end
               end
               for j = 1, 4 do
                  local vertex1 = screenVertices[j]
                  local vertex2 = screenVertices[j + 4]
                  if vertex1 ~= nil and vertex2 ~= nil then
                     draw_Line(vertex1.x, vertex1.y, vertex2.x, vertex2.y)
                  end
               end
            end
         end
      end
   end
end

local function OnUnload() -- Called when the script is unloaded
   ngl = nil
   currentTarget = nil
   vPath = nil

   ---@diagnostic disable-next-line: cast-local-type
   projectileSimulation, projectileSimulation2 = nil, nil

   collectgarbage("collect")
   client.Command('play "ui/buttonclickrelease"', true) -- Play the "buttonclickrelease" sound
end

callbacks.Register("CreateMove", OnCreateMove)
callbacks.Register("CreateMove", CreateMove_PredictInBackground) -- from my testing, without it being run in the background its way less accurate

callbacks.Register("Unload", OnUnload)

callbacks.Register("Draw", OnDraw)
--[[ Play sound when loaded ]]                --
client.Command('play "ui/buttonclick"', true) -- Play the "buttonclick" sound when the script is loaded
local Menu = { -- this is the config that will be loaded every time u load the script

   tabs = {    -- dont touch this, this is just for managing the tabs in the menu
      Main = true,
      Advanced = false,
      Visuals = false,
   },

   Main = {
      AimKey = gui.GetValue("aim key"),
      AutoShoot = gui.GetValue("auto shoot") == 1 and true or false,
      MinDistance = 100,
      MaxDistance = 1500,
      MinHitchance = 40,
   },

   Advanced = {
      SplashPrediction = true,
      SplashAccuracy = 6,
      PredTicks = 77,
      Hitchance_Accuracy = 17,
      AccuracyWeight = 5,
      StrafePrediction = false,
      StrafeSamples = 17,
      ProjectileSegments = 7,
      Aim_Modes = {
         Leading = true,
         trailing = false,
      },
   },

   Visuals = {
      Active = true,
      VisualizePath = true,
      Path_styles = { "Line", "Alt Line", "Dashed" },
      Path_styles_selected = 2,
      VisualizeHitchance = false,
      VisualizeProjectile = false,
      VisualizeHitPos = false,
      Crosshair = false,
      NccPred = false
   },
}

--- download my general purpose lib straight from the repo
---@module "ngl"
local ngl = load(http.Get("https://raw.githubusercontent.com/uosq/lbox-ngl-lib/refs/heads/main/ngl.lua"))()

local menuLoaded, ImMenu = pcall(require, "ImMenu")
assert(menuLoaded, "ImMenu not found, please install it!")
assert(ImMenu.GetVersion() >= 0.66, "ImMenu version is too old, please update it!")

---@alias AimTarget { entity : Entity, angles : EulerAngles, factor : number }

local Hitbox = {
   Head = 1,
   Neck = 2,
   Pelvis = 4,
   Body = 5,
   Chest = 7,
   Feet = 11,
}

-- Cache API calls for optimization
local math = math
local engine = engine
local globals = globals
local table = table

local math_atan = math.atan
local math_cos = math.cos
local math_sin = math.sin
local math_sqrt = math.sqrt
local math_floor = math.floor
local math_rad = math.rad
local math_deg = math.deg
local math_acos = math.acos
local math_abs = math.abs
local math_min = math.min
local math_exp = math.exp
local math_max = math.max

local TickInterval = globals.TickInterval

local TraceLine = engine.TraceLine
local TraceHull = engine.TraceHull

local GetConVar = client.GetConVar
local WorldToScreen = client.WorldToScreen

local FindByClass = entities.FindByClass

local ipairs = ipairs

local draw_Line = draw.Line
local draw_Text = draw.Text
local draw_FilledRect = draw.FilledRect

local M_RADPI = 180 / math.pi
local function isNaN(number) return number ~= number end

local latency, lerp, strafeAngles, hitChance, lastPosition, priorPrediction
local hitChanceRecords, vPath, vHitbox, MAX_ANGLE_HISTORY, MAX_CENTER_HISTORY
local strafeAngleHistories, centerHistories = {},
    {} --- history of strafe angles for each player, and history of center directions for each player

latency, lerp, hitChance = 0, 0, 0
lastPosition, priorPrediction, hitChanceRecords, vPath = {}, {}, {}, {}
---@type number[]
strafeAngles = {}

MAX_ANGLE_HISTORY = Menu.Advanced.StrafeSamples
MAX_CENTER_HISTORY = 5

--- what are these magical numbers?
--- StudioBBox Mins and Maxs?
vHitbox = { Vector3(-22, -22, 0), Vector3(22, 22, 80) }

local vUp = Vector3(0, 0, 1)
local GROUND_COLLISION_ANGLE_LOW = 45
local GROUND_COLLISION_ANGLE_HIGH = 60
local FORWARD_COLLISION_ANGLE = 55

local projectileSimulation = {}
local projectileSimulation2 = Vector3()

local EMPTY_VECTOR = Vector3() -- Represents an empty vector for zero velocity cases

---@param player Entity
local function CalcStrafe(player)
   local strafes = {}
   local index = player:GetIndex()
   --- assume every player in players table is valid (not dormant, alive, not same team as localplayer, etc)
   local velocityAngle = player:EstimateAbsVelocity():Angles() --- angle of velocity vector

   --- initialize angle history if neeeded
   strafeAngleHistories[index] = strafeAngleHistories[index] or {}
   centerHistories[index] = centerHistories[index] or {}

   --- delta velocity angle
   local delta = velocityAngle.y - (strafeAngleHistories[index][#strafeAngleHistories[index]] or 0)
   --- normalize the angle
   delta = (delta % 360) > 180 and delta - 360 or delta

   --strafeAngleHistories[index][#strafeAngleHistories[index]+1] = velocityAngle.y yeah no this is too ugly even for me
   table.insert(strafeAngleHistories[index], velocityAngle.y)
   if #strafeAngleHistories[index] > MAX_ANGLE_HISTORY then
      table.remove(strafeAngleHistories[index], 1)
   end

   if #strafeAngleHistories[index] >= 3 then
      local center = velocityAngle.y -- Use the most recent angle as the center
      table.insert(centerHistories[index], center)

      if #centerHistories[index] > MAX_CENTER_HISTORY then
         table.remove(centerHistories[index], 1)
      end

      -- Use the most recent center direction
      local mostRecentCenter = centerHistories[index][#centerHistories[index]]
      local currentPos = player:GetAbsOrigin()
      local currentVelocity = player:EstimateAbsVelocity()

      -- Predict next position based on velocity and strafe pattern
      local predictedPos = Vector3(
         currentPos.x + (currentVelocity.x * globals.AbsoluteFrameTime()),
         currentPos.y + (currentVelocity.y * globals.AbsoluteFrameTime()),
         currentPos.z + (currentVelocity.z * globals.AbsoluteFrameTime())
      )

      strafes = {
         currentPos = currentPos,
         predictedPos = predictedPos,
         strafeCenter = mostRecentCenter,
         deltaAngle = delta
      }
   end

   return strafes
end

-- Normalize vector function
local function Normalize(Vector)
   return Vector / Vector:Length()
end

-- Rotate vector function
local function RotateVector(vector, angle)
   local rad = math_rad(angle)
   local cosAngle = math_cos(rad)
   local sinAngle = math_sin(rad)
   return Vector3(
      vector.x * cosAngle - vector.y * sinAngle,
      vector.x * sinAngle + vector.y * cosAngle,
      vector.z
   )
end

-- Helper function for forward collision
local function handleForwardCollision(vel, wallTrace)
   local normal = wallTrace.plane
   local angle = math_deg(math_acos(normal:Dot(vUp)))
   if angle > FORWARD_COLLISION_ANGLE then
      local dot = vel:Dot(normal)
      vel = vel - normal * dot
   end
   return wallTrace.endpos.x, wallTrace.endpos.y
end

-- Helper function for ground collision
local function handleGroundCollision(vel, groundTrace)
   local normal = groundTrace.plane
   local angle = math_deg(math_acos(normal:Dot(vUp)))
   local onGround = false
   if angle < GROUND_COLLISION_ANGLE_LOW then
      onGround = true
   elseif angle < GROUND_COLLISION_ANGLE_HIGH then
      vel.x, vel.y, vel.z = 0, 0, 0
   else
      local dot = vel:Dot(normal)
      vel = vel - normal * dot
      onGround = true
   end
   if onGround then vel.z = 0 end
   return groundTrace.endpos, onGround
end

local function calculateHitChancePercentage(lastPredictedPos, currentPos)
   if not lastPredictedPos then
      print("lastPosition is NIL ~~!!!!")
      return 0
   end

   -- Calculate horizontal distance (2D distance on the X-Y plane)
   local horizontalDistance = math_sqrt((currentPos.x - lastPredictedPos.x) ^ 2 + (currentPos.y - lastPredictedPos.y) ^
      2)

   -- Calculate vertical distance with an allowance for vertical movement
   local verticalDistance = math_abs(currentPos.z - lastPredictedPos.z)

   -- Define maximum acceptable distances
   local maxHorizontalDistance = 12 -- Max acceptable horizontal distance in units
   local maxVerticalDistance = 45   -- Max acceptable vertical distance in units

   -- Normalize the distances to a 0-1 scale
   local horizontalFactor = math_min(horizontalDistance / maxHorizontalDistance, 1)
   local verticalFactor = math_min(verticalDistance / maxVerticalDistance, 1)

   -- Calculate the hit chance as a percentage
   local overallFactor = (horizontalFactor + verticalFactor) / 2

   -- Convert to a percentage where 100% is perfect and 0% is a miss
   local hitChancePercentage = (1 - overallFactor) * 100

   return hitChancePercentage
end

-- Helper function to check path clearance for side collisions
local function checkPathClearance(dest, direction, angle, distance, origin, target)
   -- Function to determine if an entity should be hit
   local shouldhitentity = function(entity) return entity:GetIndex() ~= target:GetIndex() end

   -- Calculate the point based on direction and angle
   local point = dest + RotateVector(direction, angle) * distance

   -- Perform a trace line downwards from the calculated point to ensure it's on solid ground
   local traceDown = TraceLine(point, point + Vector3(0, 0, -100), 100679691, shouldhitentity)

   -- Check if the end point is within an acceptable range to the target
   local distanceToTarget = (traceDown.endpos - dest):Length()
   if distanceToTarget > distance then
      local excessDistance = distanceToTarget - distance
      local directionToDest = Normalize(traceDown.endpos - dest)
      traceDown.endpos = traceDown.endpos + directionToDest * excessDistance
   end

   -- Perform a final visibility check from the origin to the destination
   local visibilityCheck = TraceLine(origin, dest, 100679691, shouldhitentity)
   if visibilityCheck.fraction > 0.9 then
      return false
   end

   return true, traceDown.endpos -- Path is clear and within range
end

-- Function to find the best shooting position
local function FindBestShootingPosition(origin, dest, target, BlastRadius)
   -- Helper function to check path clearance in a given direction and angle
   local function checkPath(direction, angle, distance)
      local point = dest + RotateVector(direction, angle) * distance

      -- Perform a trace line from origin to the point
      local traceLineOriginToPoint = TraceLine(origin, point, 100679691,
         function(entity) return entity:GetIndex() ~= target:GetIndex() end)

      -- Return whether the path is clear and the actual end position
      return traceLineOriginToPoint.fraction > 0.9, traceLineOriginToPoint.endpos
   end

   -- Perform an initial trace from origin to destination
   local initialTrace = TraceLine(origin, dest, 100679691,
      function(entity) return entity:GetIndex() ~= target:GetIndex() end)

   -- If the initial trace hits something other than the target, find a better shooting position
   if initialTrace.fraction < 1 and initialTrace.entity:GetIndex() ~= target:GetIndex() then
      local direction = Normalize(dest - origin)

      -- Check initial clearance for left and right using checkPathClearance
      local leftClear, leftMaxPoint = checkPathClearance(dest, direction, -90, BlastRadius, origin, target)
      local rightClear, rightMaxPoint = checkPathClearance(dest, direction, 90, BlastRadius, origin, target)

      -- Determine the side to perform binary search on and its maximum distance point
      local searchSide = nil
      local maxDistancePoint = nil

      if leftClear and rightClear then
         -- Determine which side is closer to the destination
         local leftDistance = (leftMaxPoint - dest):Length()
         local rightDistance = (rightMaxPoint - dest):Length()

         if leftDistance < rightDistance then
            searchSide = -90
            maxDistancePoint = leftMaxPoint
         else
            searchSide = 90
            maxDistancePoint = rightMaxPoint
         end
      elseif leftClear then
         searchSide = -90
         maxDistancePoint = leftMaxPoint
      elseif rightClear then
         searchSide = 90
         maxDistancePoint = rightMaxPoint
      end

      -- Perform binary search to find the closest shootable point to the destination
      if searchSide and maxDistancePoint then
         local minDistance = 0
         local maxDistance = (maxDistancePoint - dest):Length()
         local iterations = Menu.Advanced.SplashAccuracy or 5
         local bestPoint = maxDistancePoint -- Start with the farthest point
         local bestDistance = maxDistance

         for i = 1, iterations do
            local midDistance = (minDistance + maxDistance) / 2
            local isClear, midPoint = checkPath(direction, searchSide, midDistance)

            if isClear then
               local distanceToDest = (midPoint - dest):Length()
               if distanceToDest < bestDistance then
                  bestDistance = distanceToDest
                  bestPoint = midPoint
               end
               maxDistance = midDistance
            else
               minDistance = midDistance
            end
         end

         if bestPoint then
            projectileSimulation2 = bestPoint
            return bestPoint
         end
      end

      return false -- No valid shooting position found
   end

   return dest -- If the initial trace is clear, return the destination as the best shooting position
end

-- Precompute and cache frequently used constants and empty vectors
local MASK_PLAYERSOLID = 100679691 -- Example value; replace with the actual value from your environment for tracing
local FULL_HIT_FRACTION = 1.0      -- Represents a full hit fraction in trace results
local DRAG_COEFFICIENT = 0.029374  -- Combined drag coefficients for drag simulation

-- Function to solve projectile trajectory and return the necessary angles and time to hit a target
---@param origin Vector3  -- The starting position of the projectile
---@param dest Vector3  -- The destination or target position
---@param speed number  -- The initial speed of the projectile
---@param gravity number  -- The gravity factor affecting the projectile
---@param sv_gravity number  -- The server's gravity setting
---@param target Entity  -- The target entity to avoid hitting with the projectile
---@param timeToHit number  -- The maximum allowed time to hit the target
---@return { angles: EulerAngles, time: number, Prediction: Vector3, Positions: table }|false?  -- Returns calculated angles, time, predicted final position, and the flight path positions
local function SolveProjectile(origin, dest, speed, gravity, sv_gravity, target, timeToHit)
   -- Calculate the direction vector from origin to destination
   local direction = dest - origin

   -- Calculate squared speed for later use in equations
   local speed_squared = speed * speed

   -- Calculate the effective gravity based on server gravity settings and the specified gravity factor
   local effective_gravity = sv_gravity * gravity

   -- Calculate the horizontal (2D) distance and vertical (Z-axis) distance between origin and destination
   local horizontal_distance = direction:Length2D()
   local vertical_distance = direction.z

   -- Entity filter function to avoid hitting the target itself
   local shouldHitEntity = function(entity)
      return entity:GetIndex() ~= target:GetIndex() or entity:GetTeamNumber() ~= target:GetTeamNumber()
   end

   -- Case for when there is no gravity (e.g., hitscan projectiles)
   if effective_gravity == 0 then
      -- Calculate the time to hit based on speed and distance
      local time_to_target = direction:Length() / speed
      if time_to_target > timeToHit then
         return false -- Projectile will fly out of range, so return false
      end

      -- Perform a trace line to check if the path is clear
      local trace = TraceLine(origin, dest, MASK_PLAYERSOLID)
      if trace.fraction ~= FULL_HIT_FRACTION and trace.entity:GetName() ~= target:GetName() then
         return false -- Path is obstructed, so return false
      end

      projectileSimulation = { origin, trace.endpos }

      -- Return the result with no gravity calculations
      return {
         angles = ngl.CalcAngle(origin, dest),
         time = time_to_target,
         Prediction = dest,
         Positions = { origin, dest }
      }
   else
      -- Ballistic arc calculation when gravity is present

      -- Calculate the term related to gravity and horizontal distance squared
      local gravity_horizontal_squared = effective_gravity * horizontal_distance * horizontal_distance

      -- Solve the quadratic equation for projectile motion
      local discriminant = speed_squared * speed_squared -
          effective_gravity * (gravity_horizontal_squared + 2 * vertical_distance * speed_squared)
      if discriminant < 0 then return nil end -- No real solution, so return nil

      -- Calculate the pitch and yaw angles required for the projectile to reach the target
      local sqrt_discriminant = math_sqrt(discriminant)
      local pitch_angle = math_atan((speed_squared - sqrt_discriminant) / (effective_gravity * horizontal_distance))
      local yaw_angle = math_atan(direction.y, direction.x)

      if isNaN(pitch_angle) or isNaN(yaw_angle) then return nil end

      -- Convert the pitch and yaw into Euler angles
      local calculated_angles = EulerAngles(pitch_angle * -M_RADPI, yaw_angle * M_RADPI)

      -- Calculate the time it takes for the projectile to reach the target
      local time_to_target = horizontal_distance / (math_cos(pitch_angle) * speed)

      if time_to_target > timeToHit then
         return false -- Projectile will fly out of range, so return false
      end

      -- Define the number of segments to divide the trajectory into for simulation (default is 2)
      local number_of_segments = math_max(1, Menu.Advanced.ProjectileSegments or 2)
      local segment_duration = time_to_target / number_of_segments
      local current_position = origin
      local current_velocity = speed

      -- Table to store positions along the projectile's path
      projectileSimulation = { current_position }

      -- Simulate the projectile's flight path
      for segment = 1, number_of_segments do
         local time_segment = segment * segment_duration

         -- Apply drag to the current velocity over time
         current_velocity = current_velocity * math_exp(-DRAG_COEFFICIENT * time_segment)

         -- Calculate the new position based on current velocity, pitch, yaw, and gravity
         local horizontal_displacement = current_velocity * math_cos(pitch_angle) * time_segment
         local vertical_displacement = current_velocity * math_sin(pitch_angle) * time_segment -
             0.5 * effective_gravity * time_segment * time_segment
         local new_position = origin +
             Vector3(horizontal_displacement * math_cos(yaw_angle), horizontal_displacement * math_sin(yaw_angle),
                vertical_displacement)

         -- Perform a trace to check for collisions
         local trace = TraceLine(current_position, new_position, MASK_PLAYERSOLID, shouldHitEntity)

         -- Save the new position to the projectile path
         table.insert(projectileSimulation, new_position)

         -- Check if the projectile collided with something that isn't the target
         if trace.fraction < FULL_HIT_FRACTION and trace.entity ~= target then
            return false -- Collision detected, exit the loop
         end

         -- Update the current position for the next segment
         current_position = new_position
      end

      -- Return the calculated angles, time to target, final predicted position, and all positions along the path
      return {
         angles = calculated_angles,
         time = time_to_target,
         Prediction = current_position,
         Positions = projectileSimulation
      }
   end
end

-- Function to calculate the trust factor based on the number of records
local function calculateTrustFactor(numRecords, maxRecords, growthRate)
   -- Ensure we avoid division by zero
   if maxRecords == 0 then
      return 0
   end

   -- Calculate the ratio of current records to maximum records
   local ratio = numRecords / maxRecords

   -- Apply a logarithmic function to grow the trust factor
   local trustFactor = math.log(1 + ratio * (math.exp(growthRate) - 1)) / growthRate

   -- Ensure the trust factor is capped at 1
   if trustFactor > 1 then
      trustFactor = 1
   end

   -- Round the trust factor to 2 decimal places
   trustFactor = math_floor((trustFactor * 100) + 0.5) / 100

   return trustFactor
end

-- Function to calculate the adjusted hit chance
local function calculateAdjustedHitChance(hitChance, trustFactor)
   -- Apply the trust factor as a multiplier to the hit chance
   return math_floor((hitChance * trustFactor * 100) + 0.5) / 100
end

local function GetBonePosition(entity, hitbox)
   local model = entity:GetModel()
   local studioHdr = models.GetStudioModel(model)

   local myHitBoxSet = entity:GetPropInt("m_nHitboxSet")
   local hitboxSet = studioHdr:GetHitboxSet(myHitBoxSet)
   local hitboxes = hitboxSet:GetHitboxes()
   local hitbox = hitboxes[hitbox]

   local boneMatrices = entity:SetupBones()
   local bone = hitbox:GetBone()
   local boneMatrix = boneMatrices[bone]

   if boneMatrix == nil then return nil end
   local bonePos = Vector3(boneMatrix[1][4], boneMatrix[2][4], boneMatrix[3][4])
   return bonePos
end

---@param player Entity
local function GetBodyPosition(player)
   return GetBonePosition(player, Hitbox.Pelvis)
end

local function GetHeadPosition(player)
   return GetBonePosition(player, Hitbox.Head)
end

--- i wish there was a better way to do this, but i cant think of one for now
local function GetFeetPosition(player)
   return player:GetAbsOrigin() + Vector3(0, 0, 10)
end

---@param weapon Entity
---@param player Entity
local function GetAimPos(weapon, player)
   --local aimPos = weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ROCKET and GetFeetPosition(player) or weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ARROW and GetHeadPosition(player) or GetBodyPosition(player)
   if weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ROCKET
       or weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_PIPEBOMB then
      return GetFeetPosition(player)
   elseif weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_ARROW then
      local class = player:GetPropInt("m_PlayerClass", "m_iClass")
      --- player is a medic or sniper?
      if class == 2 then     --- medic
         return GetBodyPosition(player)
      elseif class == 5 then --- sniper
         return GetHeadPosition(player)
      end
   else
      return GetBodyPosition(player)
   end
end

-- Main function
local function CheckProjectileTarget(me, weapon, player)
   local tick_interval = TickInterval()
   local shootPos = ngl.GetShootPos(me)
   local aimPos = GetAimPos(weapon, player)
   if not aimPos then return nil end
   local aimOffset = aimPos - player:GetAbsOrigin()
   local gravity = GetConVar("sv_gravity")
   local stepSize = player:GetPropFloat("localdata", "m_flStepSize")
   local strafeAngle = Menu.Advanced.StrafePrediction and strafeAngles[player:GetIndex()] or nil
   local vStep = Vector3(0, 0, stepSize / 2)
   vPath = {}
   local lastP, lastV, lastG = player:GetAbsOrigin(), player:EstimateAbsVelocity(),
       player:GetPropInt("m_fFlags") & FL_ONGROUND == 1
   local BlastRadius = 150

   -- trace ignore simulated player
   local function shouldHitEntity(entity)
      return entity:GetIndex() ~= player:GetIndex() or
          entity:GetTeamNumber() ~= player:GetTeamNumber()
   end

   -- Check initial conditions
   local projInfo = ngl.GetProjectileInfo(weapon)
   if not projInfo or not gravity or not stepSize then return nil end

   local PredTicks = Menu.Advanced.PredTicks

   local speed = projInfo[1]
   if vector.Distance(aimPos, player:GetAbsOrigin()) > PredTicks * speed then return nil end

   local targetAngles, fov

   -- Initialize storage for predictions if not already initialized
   if not lastPosition[player:GetIndex()] then lastPosition[player:GetIndex()] = {} end
   if not priorPrediction[player:GetIndex()] then priorPrediction[player:GetIndex()] = {} end
   if not hitChanceRecords[player:GetIndex()] then hitChanceRecords[player:GetIndex()] = {} end

   -- Variables to accumulate hit chances
   local totalHitChance = 0
   local tickCount = 0

   -- Main Loop for Prediction and Projectile Calculations
   for i = 1, PredTicks * 2 do
      local pos = lastP + lastV * tick_interval
      local vel = lastV
      local onGround = lastG

      -- Apply strafeAngle
      if strafeAngle then
         local ang = vel:Angles()
         ang.y = ang.y + strafeAngle
         vel = ang:Forward() * vel:Length()
      end

      -- Forward Collision
      local wallTrace = TraceHull(lastP + vStep, pos + vStep, vHitbox[1], vHitbox[2], MASK_PLAYERSOLID,
         shouldHitEntity)
      if wallTrace.fraction < 1 then
         pos.x, pos.y = handleForwardCollision(vel, wallTrace)
      end

      -- Ground Collision
      local downStep = onGround and vStep or Vector3()
      local groundTrace = TraceHull(pos + vStep, pos - downStep, vHitbox[1], vHitbox[2], MASK_PLAYERSOLID,
         shouldHitEntity)
      if groundTrace.fraction < 1 then
         pos, onGround = handleGroundCollision(vel, groundTrace)
      else
         onGround = false
      end

      -- Apply gravity if not on ground
      if not onGround then
         vel.z = vel.z - gravity * tick_interval
      end

      lastP, lastV, lastG = pos, vel, onGround

      -- Projectile Targeting Logic
      pos = lastP + aimOffset
      vPath[i] = pos -- save path for visuals

      -- Hitchance check and synchronization of predictions
      if i <= PredTicks then
         local currentTick = PredTicks - i -- Determine which tick in the future we're currently predicting

         -- Store the last prediction of the current tick
         lastPosition[player:GetIndex()][currentTick] = priorPrediction[player:GetIndex()][currentTick] or pos

         -- Update priorPrediction with the current predicted position for this tick
         priorPrediction[player:GetIndex()][currentTick] = pos

         -- Calculate hit chance for the current tick
         local hitChance1 = calculateHitChancePercentage(lastPosition[player:GetIndex()][currentTick],
            priorPrediction[player:GetIndex()][currentTick])

         -- Insert the hit chance record
         table.insert(hitChanceRecords[player:GetIndex()], hitChance1)

         -- Ensure the number of records does not exceed the maximum allowed
         local maxRecords = Menu.Advanced.Hitchance_Accuracy
         if #hitChanceRecords[player:GetIndex()] > maxRecords then
            table.remove(hitChanceRecords[player:GetIndex()], 1) -- Remove the oldest record
         end

         -- Accumulate hit chance and tick count
         totalHitChance = totalHitChance + hitChance1
         tickCount = tickCount + 1
      end

      -- Solve the projectile based on the current position
      local solution = SolveProjectile(shootPos, pos, projInfo[1], projInfo[2], gravity, player,
         PredTicks * tick_interval)
      if solution == nil then goto continue end

      if not solution then
         if Menu.Advanced.SplashPrediction and projInfo[2] == 0 then
            local bestPos = FindBestShootingPosition(shootPos, pos, player, BlastRadius)
            if bestPos then
               solution = SolveProjectile(shootPos, bestPos, projInfo[1], projInfo[2], gravity, player,
                  PredTicks * tick_interval)
            end
         else
            return nil
         end
      end

      local time
      if solution and solution.time then
         time = solution.time + latency + lerp
      else
         return nil
      end

      local ticks = (time * 66.67) + 1
      if ticks > i then goto continue end

      targetAngles = solution.angles
      break
      ::continue::
   end

   -- Calculate the average hit chance and set the global hitChance variable
   if tickCount > 0 then
      hitChance = totalHitChance / tickCount
   else
      hitChance = 0
   end

   -- Calculate trust factor based on the number of records
   local numRecords = #hitChanceRecords[player:GetIndex()]
   local growthRate = Menu.Advanced.AccuracyWeight or 1 -- Customize as needed
   local trustFactor = calculateTrustFactor(numRecords, Menu.Advanced.Hitchance_Accuracy, growthRate)

   -- Adjust the average hit chance based on trust factor
   hitChance = calculateAdjustedHitChance(hitChance, trustFactor)

   -- Check if the average adjusted hit chance meets the minimum required threshold
   if hitChance < Menu.Main.MinHitchance then
      return nil -- If not, return nil to indicate that the prediction is not reliable
   end

   if not targetAngles or (player:GetAbsOrigin() - me:GetAbsOrigin()):Length() < 100 or not lastPosition[player:GetIndex()] then
      return nil
   end

   return { entity = player, angles = targetAngles, factor = fov, Prediction = vPath[#vPath] }
end

---@param name string
local function bGetGUIValue(name)
   return gui.GetValue(name) == 1
end

---@param localplayer Entity
---@param weapon Entity
local function RunBullet(localplayer, weapon, target)
   --- we will only run stuff when lbox aimbot is turned off
   local aimPos = ngl.GetAimPosition(localplayer, weapon)
   local shootPos = ngl.GetShootPos(localplayer)

   local targetPos = ngl.GetHitboxPos(target, aimPos)
   if not targetPos then return end

   --local angle = ngl.CalcAngle(shootPos, targetPos)
   --- multipoint :3
   local angle = aimPos == ngl.HitboxBoneIndex.Body and ngl.ScanBody(localplayer, target) or
       ngl.ScanHead(localplayer, target)
   if not angle then return end

   if not ngl.VisPosHitboxIdOut(target, shootPos, angle.pos) then return end

   local fov = ngl.CalcFov(engine:GetViewAngles(), angle.angle)

   if fov > gui.GetValue("aim fov") then return end

   if gui.GetValue("norecoil") then
      local punchangle = localplayer:GetPropVector("m_vecPunchAngle")
      angle.angle = angle.angle - punchangle
   end

   return { angles = angle.angle, factor = fov }
end

---@param localplayer Entity
---@param weapon Entity
---@param target Entity
local function RunMelee(localplayer, weapon, target)
   local shootPos = ngl.GetShootPos(localplayer)
   local aimPos = ngl.GetAimPosition(localplayer, weapon)

   local vis_check = true

   local method = gui.GetValue("melee aimbot")
   if method == "rage" then
      vis_check = false
   end

   local targetPos = ngl.GetHitboxPos(target, aimPos)
   if not targetPos then return end

   if vis_check then
      local trace = weapon:DoSwingTrace()
      --- if not visible from where we hit, dont calculate angle and fov
      if trace.entity ~= target then return end
   end

   local angle = ngl.CalcAngle(shootPos, targetPos)
   local fov = ngl.CalcFov(engine:GetViewAngles(), angle)
   if fov > gui.GetValue("aim fov") then return end

   if gui.GetValue("norecoil") then
      local punchangle = localplayer:GetPropVector("m_vecPunchAngle")
      angle = angle - punchangle
   end

   return { angles = angle, factor = fov }
end

---@param me Entity
---@param weapon Entity
local function GetBestTarget(me, weapon)
   local players = FindByClass("CTFPlayer")
   local bestTarget = nil
   local bestFactor = 0
   local localPlayerOrigin = me:GetAbsOrigin()
   local localPlayerViewAngles = engine.GetViewAngles()

   for _, player in pairs(players) do
      if player:GetTeamNumber() == me:GetTeamNumber() then goto continue end
      if player:IsDormant() or not player:IsAlive() then goto continue end
      if player:InCond(E_TFCOND.TFCond_Cloaked) and bGetGUIValue("ignore cloaked") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Taunting) and bGetGUIValue("ignore taunting") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Disguised) and bGetGUIValue("ignore disguised") then goto continue end
      if player:InCond(E_TFCOND.TFCond_DeadRingered) and bGetGUIValue("ignore deadringer") then goto continue end
      if player:InCond(E_TFCOND.TFCond_Bonked) and bGetGUIValue("ignore bonked") then goto continue end

      local playerOrigin = player:GetAbsOrigin()

      local angles = ngl.CalcAngle(localPlayerOrigin, playerOrigin)
      local fov = ngl.CalcFov(angles, localPlayerViewAngles)

      if fov > gui.GetValue("aim fov") then
         goto continue
      end

      local distance = math_abs(playerOrigin.x - localPlayerOrigin.x) +
          math_abs(playerOrigin.y - localPlayerOrigin.y) +
          math_abs(playerOrigin.z - localPlayerOrigin.z)

      local distanceFactor = ngl.RemapValClamped(distance, 50, 2500, 1, 0.09)
      local fovFactor = ngl.RemapValClamped(fov, 0, gui.GetValue("aim fov"), 1, 0.7)
      local isVisible = ngl.VisPos(player, localPlayerOrigin + Vector3(0, 0, 75), playerOrigin + Vector3(0, 0, 75))
      local visibilityFactor = isVisible and 1 or 0.5
      local factor = fovFactor * visibilityFactor * distanceFactor

      if factor > bestFactor then
         bestTarget = player
         bestFactor = factor
      end

      ::continue::
   end

   if bestTarget then
      -- Projectile weapon
      if weapon:IsMeleeWeapon() then
         return RunMelee(me, weapon, bestTarget)
      end
      if weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_BULLET then
         return RunBullet(me, weapon, bestTarget)
      else --- not a hitscan weapon, so we predict it
         return CheckProjectileTarget(me, weapon, bestTarget)
      end
   else
      return nil
   end
end

---@param userCmd UserCmd
local function OnCreateMove(userCmd)
   --- check if aimbot is enabled on lbox
   if gui.GetValue("aim bot") == 1 then return end

   if engine.IsChatOpen() or engine.Con_IsVisible() or engine.IsGameUIVisible() then return end
   if not input.IsButtonDown(gui.GetValue("aim key")) then
      return
   end

   projectileSimulation2 = EMPTY_VECTOR

   local me = entities:GetLocalPlayer()
   if not me or not me:IsAlive() then return end

   local weapon = ngl.GetCurrentWeapon(me)
   if not weapon then return end

   if not ngl.CanWeaponShoot(me, weapon) then return end

   local netchannel = clientstate.GetNetChannel()
   if not netchannel then return end

   -- Get current latency
   local latIn, latOut = netchannel:GetLatency(E_Flows.FLOW_INCOMING), netchannel:GetLatency(E_Flows.FLOW_OUTGOING)
   latency = (latIn or 0) + (latOut or 0)

   -- Get current lerp
   lerp = GetConVar("cl_interp") or 0

   -- Get the best target
   local currentTarget = GetBestTarget(me, weapon)
   if currentTarget == nil then
      return
   end

   local isHitscan = weapon:GetWeaponProjectileType() == E_ProjectileType.TF_PROJECTILE_BULLET
   local isMelee = weapon:IsMeleeWeapon()
   local hitscanMethod, projMethod = gui.GetValue("aim method"), gui.GetValue("aim method (projectile)")

   -- Calculate strafe angles (optional)
   if Menu.Advanced.StrafePrediction and not isHitscan and not isMelee then
      local strafe = CalcStrafe(me)
      if strafe then
         strafeAngles[currentTarget.entity:GetIndex()] = strafe.deltaAngle
      end
   end

   -- Auto Shoot
   if bGetGUIValue("auto shoot") then
      if weapon:GetWeaponID() == TF_WEAPON_COMPOUND_BOW or weapon:GetWeaponID() == TF_WEAPON_PIPEBOMBLAUNCHER then
         -- Huntsman
         if weapon:GetChargeBeginTime() > 0 then
            userCmd.buttons = userCmd.buttons & ~IN_ATTACK
         else
            userCmd.buttons = userCmd.buttons | IN_ATTACK
         end
      else
         -- Normal weapon
         userCmd.buttons = userCmd.buttons | IN_ATTACK
      end
   end

   if (userCmd.buttons & IN_ATTACK ~= 0) then
      -- Aim at the target
      userCmd:SetViewAngles(currentTarget.angles:Unpack())
      userCmd.sendpacket = (isHitscan and projMethod == "silent +") or isMelee

      if (isHitscan and (hitscanMethod == "plain" or hitscanMethod == "smooth"))
          or (not isHitscan and (projMethod == "plain" or projMethod == "smooth")) then
         engine.SetViewAngles(EulerAngles(currentTarget.angles:Unpack()))
      end
   end

   currentTarget = nil
end

local font = draw.CreateFont("Verdana", 12, 400, FONTFLAG_OUTLINE)
draw.SetFont(font)

local function L_line(start_pos, end_pos, secondary_line_size)
   if not (start_pos and end_pos) then
      return
   end
   local direction = end_pos - start_pos
   local direction_length = direction:Length()
   if direction_length == 0 then
      return
   end
   local normalized_direction = Normalize(direction)
   local perpendicular = Vector3(normalized_direction.y, -normalized_direction.x, 0) * secondary_line_size
   local w2s_start_pos = WorldToScreen(start_pos)
   local w2s_end_pos = WorldToScreen(end_pos)
   if not (w2s_start_pos and w2s_end_pos) then
      return
   end
   local secondary_line_end_pos = start_pos + perpendicular
   local w2s_secondary_line_end_pos = WorldToScreen(secondary_line_end_pos)
   if w2s_secondary_line_end_pos then
      draw_Line(w2s_start_pos[1], w2s_start_pos[2], w2s_end_pos[1], w2s_end_pos[2])
      draw_Line(w2s_start_pos[1], w2s_start_pos[2], w2s_secondary_line_end_pos[1], w2s_secondary_line_end_pos[2])
   end
end

local hitPos = {}
local function PlayerHurtEvent(event)
   if (event:GetName() == 'player_hurt') and Menu.Visuals.VisualizeHitPos then
      local localPlayer = entities.GetLocalPlayer();
      if not localPlayer then return end
      local victim = entities.GetByUserID(event:GetInt("userid"))
      if not victim then return end
      local attacker = entities.GetByUserID(event:GetInt("attacker"))
      if (attacker == nil or localPlayer:GetIndex() ~= attacker:GetIndex()) then
         return
      end
      table.insert(hitPos, 1, { box = victim:HitboxSurroundingBox(), time = globals.RealTime() })
   end
   if #hitPos > 1 then
      table.remove(hitPos)
   end
end
callbacks.Register("FireGameEvent", "PlayerHurtEvent", PlayerHurtEvent)

local clear_lines = 0

local function OnDraw()
   draw.SetFont(font)
   draw.Color(255, 255, 255, 255)

   if not input.IsButtonDown(gui.GetValue("aim key")) then
      if (globals.RealTime() > (clear_lines + 5)) then
         vPath = {}
         clear_lines = globals.RealTime()
      end
   else
      clear_lines = globals.RealTime()
   end
   -- Draw lines between the predicted positions
   if Menu.Visuals.Active and vPath then
      local startPos
      draw.SetFont(font)
      for i = 1, #vPath - 1 do
         local pos1 = vPath[i]
         local pos2 = vPath[i + 1]

         if i == 1 then
            startPos = pos1
         end

         draw.Color(255 - math_floor((hitChance / 100) * 255), math_floor((hitChance / 100) * 255), 0, 255)

         --draw predicted local position with strafe prediction
         if projectileSimulation2 and projectileSimulation2 ~= EMPTY_VECTOR then
            local screenPos = WorldToScreen(projectileSimulation2)
            if screenPos ~= nil then
               draw_Line(screenPos[1] + 10, screenPos[2], screenPos[1] - 10, screenPos[2])
               draw_Line(screenPos[1], screenPos[2] - 10, screenPos[1], screenPos[2] + 10)
            end
         end

         if Menu.Visuals.VisualizeHitchance or Menu.Visuals.Crosshair or Menu.Visuals.NccPred then
            if i == #vPath - 1 then
               local screenPos1 = WorldToScreen(pos1)
               local screenPos2 = WorldToScreen(pos2)

               if screenPos1 ~= nil and screenPos2 ~= nil then
                  if Menu.Visuals.VisualizeHitchance then
                     ---@diagnostic disable-next-line: param-type-mismatch
                     local width = draw.GetTextSize(math_floor(hitChance))
                     ---@diagnostic disable-next-line: param-type-mismatch
                     draw_Text(screenPos2[1] - math_floor(width / 2), screenPos2[2] + 20, math_floor(hitChance))
                  end
                  if Menu.Visuals.Crosshair then
                     local c_size = 8
                     draw_Line(screenPos2[1] - c_size, screenPos2[2], screenPos2[1] + c_size, screenPos2[2])
                     draw_Line(screenPos2[1], screenPos2[2] - c_size, screenPos2[1], screenPos2[2] + c_size)
                  end
                  if Menu.Visuals.NccPred then
                     local c_size = 5
                     draw_FilledRect(screenPos2[1] - c_size, screenPos2[2] - c_size, screenPos2[1] + c_size,
                        screenPos2[2] + c_size)
                     local w2s = WorldToScreen(startPos)
                     if w2s then
                        draw_Line(w2s[1], w2s[2], screenPos2[1], screenPos2[2])
                     end
                  end
               end
            end
         end

         if Menu.Visuals.VisualizePath then
            if Menu.Visuals.Path_styles_selected == 1 or Menu.Visuals.Path_styles_selected == 3 then
               local screenPos1 = WorldToScreen(pos1)
               local screenPos2 = WorldToScreen(pos2)

               if screenPos1 ~= nil and screenPos2 ~= nil and (not (Menu.Visuals.Path_styles_selected == 3) or i % 2 == 1) then
                  draw_Line(screenPos1[1], screenPos1[2], screenPos2[1], screenPos2[2])
               end
            end

            if Menu.Visuals.Path_styles_selected == 2 then
               L_line(pos1, pos2, 10)
            end

            if projectileSimulation and Menu.Visuals.VisualizeProjectile then
               for i = 1, #projectileSimulation - 1 do
                  local pos1 = projectileSimulation[i]
                  local pos2 = projectileSimulation[i + 1]

                  if pos1 and pos2 then
                     if Menu.Visuals.Path_styles_selected == 1 or Menu.Visuals.Path_styles_selected == 3 then
                        local screenPos1 = WorldToScreen(pos1)
                        local screenPos2 = WorldToScreen(pos2)

                        if screenPos1 ~= nil and screenPos2 ~= nil and (not (Menu.Visuals.Path_styles_selected == 3) or i % 2 == 1) then
                           draw_Line(screenPos1[1], screenPos1[2], screenPos2[1], screenPos2[2])
                        end
                     end
                     if Menu.Visuals.Path_styles_selected == 2 then
                        L_line(pos1, pos2, 10)
                     end
                  end
               end
            end
         end
      end

      if Menu.Visuals.VisualizeHitPos then
         for i, v in pairs(hitPos) do
            if globals.RealTime() - v.time > 1 then
               table.remove(hitPos, i)
            else
               draw.Color(255, 255, 255, 255)
               local hitboxes = v.box
               local min = hitboxes[1]
               local max = hitboxes[2]
               local vertices = {
                  Vector3(min.x, min.y, min.z),
                  Vector3(min.x, max.y, min.z),
                  Vector3(max.x, max.y, min.z),
                  Vector3(max.x, min.y, min.z),
                  Vector3(min.x, min.y, max.z),
                  Vector3(min.x, max.y, max.z),
                  Vector3(max.x, max.y, max.z),
                  Vector3(max.x, min.y, max.z)
               }
               local screenVertices = {}
               for j, vertex in ipairs(vertices) do
                  local screenPos = WorldToScreen(vertex)
                  if screenPos ~= nil then
                     screenVertices[j] = { x = screenPos[1], y = screenPos[2] }
                  end
               end
               for j = 1, 4 do
                  local vertex1 = screenVertices[j]
                  local vertex2 = screenVertices[j % 4 + 1]
                  local vertex3 = screenVertices[j + 4]
                  local vertex4 = screenVertices[(j + 4) % 4 + 5]
                  if vertex1 ~= nil and vertex2 ~= nil and vertex3 ~= nil and vertex4 ~= nil then
                     draw_Line(vertex1.x, vertex1.y, vertex2.x, vertex2.y)
                     draw_Line(vertex3.x, vertex3.y, vertex4.x, vertex4.y)
                  end
               end
               for j = 1, 4 do
                  local vertex1 = screenVertices[j]
                  local vertex2 = screenVertices[j + 4]
                  if vertex1 ~= nil and vertex2 ~= nil then
                     draw_Line(vertex1.x, vertex1.y, vertex2.x, vertex2.y)
                  end
               end
            end
         end
      end
   end

   if gui.IsMenuOpen() and ImMenu.Begin("Custom Projectile Aimbot", true) then -- managing the menu
      ImMenu.BeginFrame(1)                                                     -- tabs
      if ImMenu.Button("Main") then
         Menu.tabs.Main = true
         Menu.tabs.Advanced = false
         Menu.tabs.Visuals = false
      end

      if ImMenu.Button("Advanced") then
         Menu.tabs.Main = false
         Menu.tabs.Advanced = true
         Menu.tabs.Visuals = false
      end

      if ImMenu.Button("Visuals") then
         Menu.tabs.Main = false
         Menu.tabs.Advanced = false
         Menu.tabs.Visuals = true
      end
      ImMenu.EndFrame()

      if Menu.tabs.Main then
         ImMenu.BeginFrame(1)
         Menu.Main.MinHitchance = ImMenu.Slider("Min Hitchance", Menu.Main.MinHitchance, 1, 100)
         ImMenu.EndFrame()
      end

      if Menu.tabs.Advanced then
         ImMenu.BeginFrame(1)
         Menu.Advanced.StrafePrediction = ImMenu.Checkbox("Strafe Pred", Menu.Advanced.StrafePrediction)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.SplashPrediction = ImMenu.Checkbox("Splash Prediction", Menu.Advanced.SplashPrediction)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.SplashAccuracy = ImMenu.Slider("Splash Accuracy", Menu.Advanced.SplashAccuracy, 2, 47)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.StrafeSamples = ImMenu.Slider("Strafe Samples", Menu.Advanced.StrafeSamples, 2, 49)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.PredTicks = ImMenu.Slider("PredTicks", Menu.Advanced.PredTicks, 1, 200)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.Hitchance_Accuracy = ImMenu.Slider("Accuracy", Menu.Advanced.Hitchance_Accuracy, 1,
            Menu.Advanced.PredTicks)
         ImMenu.EndFrame()

         ImMenu.BeginFrame(1)
         Menu.Advanced.ProjectileSegments = ImMenu.Slider("projectile Simulation Segments",
            Menu.Advanced.ProjectileSegments, 3, 50)
         ImMenu.EndFrame()
      end

      if Menu.tabs.Visuals then
         ImMenu.BeginFrame(1)
         Menu.Visuals.Active = ImMenu.Checkbox("Enable", Menu.Visuals.Active)
         ImMenu.EndFrame()

         if Menu.Visuals.Active then
            ImMenu.BeginFrame(1)
            Menu.Visuals.VisualizePath = ImMenu.Checkbox("Player Path", Menu.Visuals.VisualizePath)
            Menu.Visuals.VisualizeProjectile = ImMenu.Checkbox("Projectile Simulation",
               Menu.Visuals.VisualizeProjectile)
            ImMenu.EndFrame()

            ImMenu.BeginFrame(1)
            Menu.Visuals.VisualizeHitPos = ImMenu.Checkbox("Visualize Hit Pos", Menu.Visuals.VisualizeHitPos)
            Menu.Visuals.Crosshair = ImMenu.Checkbox("Crosshair", Menu.Visuals.Crosshair)
            Menu.Visuals.NccPred = ImMenu.Checkbox("Nullcore Pred Visuals", Menu.Visuals.NccPred)
            ImMenu.EndFrame()

            ImMenu.BeginFrame(1)
            Menu.Visuals.VisualizeHitchance = ImMenu.Checkbox("Visualize Hitchance", Menu.Visuals.VisualizeHitchance)
            ImMenu.EndFrame()

            if Menu.Visuals.VisualizePath then
               ImMenu.BeginFrame(1)
               ImMenu.Text("Visualize Path Settings")
               ImMenu.EndFrame()
               ImMenu.BeginFrame(1)
               Menu.Visuals.Path_styles_selected = ImMenu.Option(Menu.Visuals.Path_styles_selected,
                  Menu.Visuals.Path_styles)
               ImMenu.EndFrame()
            end
         end
      end

      ImMenu.End()
   end
end

--[[ Remove the menu when unloaded ]]                   --
local function OnUnload()                               -- Called when the script is unloaded
   ngl = nil
   client.Command('play "ui/buttonclickrelease"', true) -- Play the "buttonclickrelease" sound
end

callbacks.Register("CreateMove", OnCreateMove)

callbacks.Register("Unload", OnUnload)

callbacks.Register("Draw", OnDraw)
--[[ Play sound when loaded ]]                --
client.Command('play "ui/buttonclick"', true) -- Play the "buttonclick" sound when the script is loaded
