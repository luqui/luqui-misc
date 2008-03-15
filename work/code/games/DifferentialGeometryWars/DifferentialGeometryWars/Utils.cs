using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace DifferentialGeometryWars
{
    class Utils
    {
        public delegate bool DeathCond<T>(T input);
        public static void IterateWithDeath<T>(LinkedList<T> list, DeathCond<T> cond) {
            LinkedListNode<T> cptr = list.First;
            while (cptr != null) {
                LinkedListNode<T> next = cptr.Next;
                if (cond(cptr.Value)) {
                    list.Remove(cptr);
                }
                cptr = cptr.Next;
            }
        }

        public static Vector2 RotateVector(float theta, Vector2 v) {
            return new Vector2( (float)Math.Cos(theta) * v.X - (float)Math.Sin(theta) * v.Y
                              , (float)Math.Sin(theta) * v.X + (float)Math.Cos(theta) * v.Y);
        }
    }
}
