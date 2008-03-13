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
            return src + lookup(src).transform(new Vector2(-dx * dirx, -dy * diry));
        }

        public Vector2[,] getEuclideanMap(Vector2 mll, Vector2 mur, int w, int h, int iters) {
            float dx = (mur.X - mll.X) / (float) w;
            float dy = (mur.Y - mll.Y) / (float) h;

            Vector2[,] map  = new Vector2[w, h];
            Vector2[,] back = new Vector2[w, h];

            Vector2 dummy = new Vector2();
            // initialize the map to the identity
            for (int i = 0; i < w; i++) {
                float srcx = mll.X + i * dx;
                for (int j = 0; j < h; j++) {
                    float srcy = mll.Y + j * dy;
                    Vector2 src = new Vector2(srcx, srcy);
                    map[i, j] = src;
                }
            }

            for (int iter = 0; iter < iters; iter++) {
                // relax the map based on the metric
                for (int i = 1; i < w-1; i++) {
                    for (int j = 1; j < h - 1; j++) {
                        back[i, j] = 0.25f * (extrap(map, dx, dy, i, j, -1, 0)
                                            + extrap(map, dx, dy, i, j, 1, 0)
                                            + extrap(map, dx, dy, i, j, 0, -1)
                                            + extrap(map, dx, dy, i, j, 0, 1));
                    }
                }
                // edges
                for (int i = 1; i < w - 1; i++) {
                    back[i, 0] = (1.0f / 3.0f) * (extrap(map, dx, dy, i, 0, -1, 0)
                                                + extrap(map, dx, dy, i, 0, 1, 0)
                                                + extrap(map, dx, dy, i, 0, 0, 1));
                    back[i, h-1] = (1.0f / 3.0f) * (extrap(map, dx, dy, i, h-1, -1, 0)
                                                  + extrap(map, dx, dy, i, h-1, 1, 0)
                                                  + extrap(map, dx, dy, i, h-1, 0, -1));
                }
                for (int j = 1; j < h - 1; j++) {
                    back[0, j] = (1.0f / 3.0f) * (extrap(map, dx, dy, 0, j, 0, -1)
                                                + extrap(map, dx, dy, 0, j, 0, 1)
                                                + extrap(map, dx, dy, 0, j, 1, 0));
                    back[w - 1, j] = (1.0f / 3.0f) * (extrap(map, dx, dy, w - 1, j, 0, -1)
                                                    + extrap(map, dx, dy, w - 1, j, 0, 1)
                                                    + extrap(map, dx, dy, w - 1, j, -1, 0));
                                              
                }
                // corners
                back[0, 0] = 0.5f * (extrap(map, dx, dy, 0, 0, 1, 0) + extrap(map, dx, dy, 0, 0, 0, 1));
                back[0, h - 1] = 0.5f * (extrap(map, dx, dy, 0, h - 1, 1, 0) + extrap(map, dx, dy, 0, h - 1, 0, -1));
                back[w - 1, 0] = 0.5f * (extrap(map, dx, dy, w - 1, 0, -1, 0) + extrap(map, dx, dy, w - 1, 0, 0, 1));
                back[w - 1, h - 1] = 0.5f * (extrap(map, dx, dy, w - 1, h - 1, -1, 0) + extrap(map, dx, dy, w - 1, h - 1, 0, -1));

                // flip buffers
                Vector2[,] tmp = map;
                map = back;
                back = tmp;
            }

            // transform buffer according to the topology
            for (int i = 0; i < w; i++) {
                for (int j = 0; j < h; j++) {
                    topology.Canonicalize(ref map[i, j], ref dummy);
                }
            }

            return map;
        }
    }
}
