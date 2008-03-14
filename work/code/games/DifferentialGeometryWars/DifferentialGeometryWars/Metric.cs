using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace DifferentialGeometryWars
{
    class Metric
    {
        public struct TangentSpace
        {
            public TangentSpace(float a, float b, float c, float d) {
                A = a; B = b; C = c; D = d;
            }

            public Vector2 transform(Vector2 v) {
                // [ A B ] [ vx ]  =  [ vx A + vy B ]
                // [ C D ] [ vy ]     [ vx C + vy D ]
                return new Vector2(v.X * A + v.Y * B, v.X * C + v.Y * D);
            }

            public Vector2 inverseTransform(Vector2 v) {
                return new Vector2(v.X * D - v.Y * B, -v.X * C + v.Y * A) / (A * D - B * C);
            }

            public float measure(Vector2 dv) {
                Vector2 Mdv = transform(dv);
                return dv.X * Mdv.X + dv.Y * Mdv.Y;
            }

            public float A;
            public float B;
            public float C;
            public float D;
        }

        TangentSpace[,] space;
        public readonly Vector2 ll;
        public readonly Vector2 ur;
        public readonly FundamentalPoly topology;

        public Metric(FundamentalPoly poly, int xres, int yres) {
            space = new TangentSpace[xres, yres];
            topology = poly;
            ll = topology.MinBound;
            ur = topology.MaxBound;

            for (int i = 0; i < xres; i++) {
                for (int j = 0; j < yres; j++) {
                    float x = i / xres;
                    float y = j / yres;
                    space[i,j] = new TangentSpace(1,0,0,1);
                }
            }
        }

        public void modifyCircle(TangentSpace mod, Vector2 center, float radius) {
            float dx = (ur.X - ll.X) / space.GetLength(0);
            float dy = (ur.Y - ll.Y) / space.GetLength(1);

            for (float x = center.X - radius; x < center.X + radius; x += dx) {
                for (float y = center.Y - radius; y < center.Y + radius; y += dy) {
                    float dist = (center - new Vector2(x, y)).Length();
                    if (dist < radius) {
                        int i, j;
                        internalLookup(new Vector2(x, y), out i, out j);
                        modifyElem(mod, (radius - dist) / radius, i, j);
                    }
                }
            }
        }

        public void modifyUniform(TangentSpace mod) {
            for (int i = 0; i < space.GetLength(0); i++) {
                for (int j = 0; j < space.GetLength(0); j++) {
                    modifyElem(mod, 1, i, j);
                }
            }
        }

        private void modifyElem(TangentSpace mod, float amt, int i, int j) {
            Vector2 newAC = mod.transform(new Vector2(space[i, j].A, space[i, j].C));
            Vector2 newBD = mod.transform(new Vector2(space[i, j].B, space[i, j].D));
            space[i, j].A = (amt * newAC.X + (1 - amt) * space[i, j].A);
            space[i, j].B = (amt * newBD.X + (1 - amt) * space[i, j].B);
            space[i, j].C = (amt * newAC.Y + (1 - amt) * space[i, j].C);
            space[i, j].D = (amt * newBD.Y + (1 - amt) * space[i, j].D);
        }

        private void internalLookup(Vector2 p, out int tx, out int ty) {
            Vector2 dummy = new Vector2();
            topology.Canonicalize(ref p, ref dummy);
            tx = (int) (space.GetLength(0) * (p.X + ll.X) / (ur.X - ll.X));
            ty = (int) (space.GetLength(1) * (p.Y + ll.Y) / (ur.Y - ll.Y));
            if (tx < 0) tx = 0;
            if (tx >= space.GetLength(0)) tx = space.GetLength(0)-1;
            if (ty < 0) ty = 0;
            if (ty >= space.GetLength(1)) ty = space.GetLength(1) - 1;
        }

        public TangentSpace lookup(Vector2 p) {
            int tx, ty;
            internalLookup(p, out tx, out ty);
            return space[tx, ty];
        }

        private Vector2 extrap(Vector2[,] map, float dx, float dy, int x, int y, int dirx, int diry) {
            Vector2 src = map[x+dirx,y+diry];
            return src + lookup(src).inverseTransform(new Vector2(-dx * dirx, -dy * diry));
        }

        struct LocIndex
        {
            public LocIndex(int xx, int yy) { x = xx; y = yy; }
            public int x;
            public int y;
        };

        public Vector2[,] getEuclideanMap(Vector2 mll, Vector2 mur, int w, int h, int x0, int y0, Vector2 m0) {
            float dx = (mur.X - mll.X) / (float) w;
            float dy = (mur.Y - mll.Y) / (float) h;

            Vector2[,] map  = new Vector2[w, h];
            bool[,] mark = new bool[w, h];

            map[x0, y0] = m0;
            Queue<LocIndex> q = new Queue<LocIndex>();
            q.Enqueue(new LocIndex(x0, y0));

            while (q.Count > 0) {
                LocIndex idx = q.Dequeue();
                if (mark[idx.x,idx.y]) { continue; }

                Vector2 accum = new Vector2();
                int neighbors = 0;
                if (idx.x > 0) {
                    if (mark[idx.x - 1, idx.y]) { neighbors++; accum += extrap(map, dx, dy, idx.x, idx.y, -1, 0); }
                    else { q.Enqueue(new LocIndex(idx.x-1, idx.y)); };
                }
                if (idx.x < w-1) {
                    if (mark[idx.x + 1, idx.y]) { neighbors++; accum += extrap(map, dx, dy, idx.x, idx.y, 1, 0); }
                    else { q.Enqueue(new LocIndex(idx.x+1, idx.y)); };
                }
                if (idx.y > 0) {
                    if (mark[idx.x, idx.y - 1]) { neighbors++; accum += extrap(map, dx, dy, idx.x, idx.y, 0, -1); }
                    else { q.Enqueue(new LocIndex(idx.x, idx.y-1)); };
                }
                if (idx.y < h-1) {
                    if (mark[idx.x, idx.y + 1]) { neighbors++; accum += extrap(map, dx, dy, idx.x, idx.y, 0, 1); }
                    else { q.Enqueue(new LocIndex(idx.x, idx.y+1)); };
                }
               

                if (neighbors > 0) {
                    map[idx.x,idx.y] = accum / neighbors;
                }
                // if neighbors == 0 then we are the center point...
                mark[idx.x,idx.y] = true;
            }


            Vector2 dummy = new Vector2();
            for (int i = 0; i < w; i++) {
                for (int j = 0; j < h; j++) {
                    topology.Canonicalize(ref map[i, j], ref dummy);
                }
            }

            return map;
        }
    }
}
