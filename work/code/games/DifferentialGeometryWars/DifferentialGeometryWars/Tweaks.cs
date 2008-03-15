using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Content;

namespace DifferentialGeometryWars
{
    class Tweaks
    {
        // Tweaks
        // Metric resolution: higher values allow for more granularity in spacetime bending
        public const int METRIC_RESX = 512;
        public const int METRIC_RESY = 512;
        // Source resolution: the resolution at which the logical space is rendered
        //   (the thing the distortion filter acts on).   Since the distortion filter
        //   is generally continuous, this is essentially "screen resolution"
        public const int SOURCE_RESX = 512;
        public const int SOURCE_RESY = 512;
        // Distortion field resolution  (costly to calculate, so is related linearly to startup time)
        public const int DISTORTION_RESX = 512;
        public const int DISTORTION_RESY = 512;
        // Control responsiveness
        public const float TURN_RESPONSE = 0.7f;
        public const float ACCEL_RESPONSE = 0.1f;
        public const float MAX_SPEED = 0.15f;
        // Bullets
        public const float BULLET_VEL = 0.6f;
        public const float BULLET_COOLDOWN = 0.2f;
        public const float BULLET_DECAY = 2.0f;
        // Turret
        public const float TURRET_RESPONSE = 4.9f;

        public static Random RAND = new Random();
        public static ContentManager CONTENT;
    }
}
