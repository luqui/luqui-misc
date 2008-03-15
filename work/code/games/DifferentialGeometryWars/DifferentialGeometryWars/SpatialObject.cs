using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace DifferentialGeometryWars
{
    abstract class SpatialObject
    {
        protected Vector2 position;
        protected Vector2 velocity;
        protected Metric metric;

        public Vector2 Position { get { return position; } }
        public Vector2 Velocity { get { return velocity; } }

        protected SpatialObject(Vector2 pos, Vector2 vel, Metric met) {
            metric = met;
            position = pos;
            velocity = vel;
        }

        virtual public void Update(float dt) {
            position += dt * metric.lookup(position).inverseTransform(velocity);
            metric.topology.Canonicalize(ref position, ref velocity);
        }

        protected Matrix GetDrawMatrix() {
            Matrix trans = Matrix.CreateTranslation(new Vector3(position.X, position.Y, 0.0f));
            Vector2 logVel = metric.lookup(position).inverseTransform(velocity);
            Matrix rot = Matrix.CreateRotationZ((float) (Math.Atan2(logVel.Y, logVel.X) - Math.PI / 2));
            return rot * trans;
        }
    }
}
