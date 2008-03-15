using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace DifferentialGeometryWars
{
    abstract class FundamentalPoly
    {
        // A bounding box around the canonical area of the polygon
        public abstract Vector2 MinBound { get; }
        public abstract Vector2 MaxBound { get; }

        // XXX this needs a different interface because we need to canonicalize
        // the turret as well.  Maybe:
        //  Vector2 CanonicalizePosition(Vector2 pos)
        //  Vector2 CanonicalizeVector(Vector2 pos, Vector2 v)
        public abstract void Canonicalize(ref Vector2 v, ref Vector2 dv);
    }

    class TorusFundamentalPoly : FundamentalPoly
    {
        // The fundamental polygon, algebraically, for a genus-1 surface (such
        // as a torus) is
        // A B A' B'

        public override Vector2 MinBound {
            get { return new Vector2(0, 0); }
        }
        public override Vector2 MaxBound {
            get { return new Vector2(1, 1);  }
        }

        public override void Canonicalize(ref Vector2 v, ref Vector2 dv) {
            while (v.X > 1) { v.X -= 1; }
            while (v.X < 0) { v.X += 1; }
            while (v.Y > 1) { v.Y -= 1; }
            while (v.Y < 0) { v.Y += 1; }
            // dv stays constant
        }
    }

    class SphereFundamentalPoly : FundamentalPoly
    {
        // The fundamental polygon for a genus-0 surface (such as a sphere)
        // is e = A A' = A B B' A'

        public override Vector2 MinBound {
            get { return new Vector2(0, 0); }
        }
        public override Vector2 MaxBound {
            get { return new Vector2(1, 1); }
        }

        private void swap(ref float a, ref float b) {
            float tmp = a;
            a = b;
            b = tmp;
        }

        public override void Canonicalize(ref Vector2 v, ref Vector2 dv) {
            while (true) {
                if      (v.X < 0) { v.X = -v.X; dv.X = -dv.X; }
                else if (v.Y < 0) { v.Y = -v.Y; dv.Y = -dv.Y; }
                else if (v.X > 1) { v.X = 2 - v.X; dv.X = -dv.X; }
                else if (v.Y > 1) { v.Y = 2 - v.Y; dv.Y = -dv.Y; }
                else { break; }

                swap(ref v.X, ref v.Y); 
                swap(ref dv.X, ref dv.Y);
                //dv = -dv;
            }
        }
    }
}
