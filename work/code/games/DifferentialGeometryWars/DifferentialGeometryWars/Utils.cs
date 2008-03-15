using System;
using System.Collections.Generic;
using System.Text;

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
    }
}
