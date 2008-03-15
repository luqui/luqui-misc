using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace DifferentialGeometryWars
{
    abstract class Enemy : SpatialObject
    {
        public Enemy(Metric metric, Vector2 pos)
            : base(pos, new Vector2(0.0f, 0.0f), metric) { }

        public abstract void Draw(DrawHelper draw);
    }
}
