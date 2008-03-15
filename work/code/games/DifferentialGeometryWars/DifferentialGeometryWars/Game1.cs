using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.GamerServices;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Graphics.PackedVector;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Net;
using Microsoft.Xna.Framework.Storage;

namespace DifferentialGeometryWars
{
    /// <summary>
    /// This is the main type for your game
    /// </summary>
    public class Game1 : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        Effect effect;
        RenderTarget2D renderTarget;
        Texture2D targetTexture;
        DrawHelper draw;
        LinkedList<Enemy> enemies;

        PlayerShip player;

        Texture2D euclideanMap;
        Metric metric;

        VertexPositionColor[] grid;

        public Game1() {
            graphics = new GraphicsDeviceManager(this);
            graphics.PreferredBackBufferWidth = 1440;
            graphics.PreferredBackBufferHeight = 900;
            graphics.IsFullScreen = true;
            Content.RootDirectory = "Content";
            Tweaks.CONTENT = Content;
        }

        protected override void Initialize() {
            // TODO: Add your initialization logic here

            base.Initialize();
        }


        protected override void LoadContent() {
            effect = Content.Load<Effect>("Effects");
            draw = new DrawHelper(graphics, effect);

            metric = new Metric(new SphereFundamentalPoly(), Tweaks.METRIC_RESX, Tweaks.METRIC_RESY);

            player = new PlayerShip(PlayerIndex.One, metric, new Vector2(0.5f, 0.5f));
            enemies = new LinkedList<Enemy>();
            for (int i = 0; i < 10; i++) {
                enemies.AddLast(new RandomMotionEnemy(metric, new Vector2((float)Tweaks.RAND.NextDouble(), (float)Tweaks.RAND.NextDouble()))) ;
            }

            renderTarget = new RenderTarget2D(graphics.GraphicsDevice, Tweaks.SOURCE_RESX, Tweaks.SOURCE_RESY, 0, SurfaceFormat.Color);
            double theta = Math.PI / 2;
            metric.modifyCircle(new Metric.TangentSpace((float)Math.Cos(theta), -(float)Math.Sin(theta), (float)Math.Sin(theta), (float)Math.Cos(theta)), new Vector2(0.4f, 0.4f), 0.4f);
            //metric.modifyCircle(new Metric.TangentSpace(-1.0f, 0.0f, 0.0f, -1.0f), new Vector2(0.75f, 0.75f), 0.2f);
            ReloadDistortionMap();

            {
                Color color = Color.DarkGreen;
                grid = new VertexPositionColor[64];
                int idx = 0;
                for (float x = 0; x < 1 && idx < 64; x += 1.0f/16.0f) {
                    grid[idx++] = new VertexPositionColor(new Vector3(x, 0, 0), color);
                    grid[idx++] = new VertexPositionColor(new Vector3(x, 1, 0), color);
                    grid[idx++] = new VertexPositionColor(new Vector3(0, x, 0), color);
                    grid[idx++] = new VertexPositionColor(new Vector3(1, x, 0), color);
                }
            }
        }

        private void ReloadDistortionMap() {
            if (euclideanMap != null) { euclideanMap.Dispose(); }
            euclideanMap = new Texture2D(graphics.GraphicsDevice, Tweaks.DISTORTION_RESX, Tweaks.DISTORTION_RESY, 0, TextureUsage.None, SurfaceFormat.Rg32);
            Vector2[,] mapData = metric.getEuclideanMap(new Vector2(-0.5f, -0.5f), new Vector2(1.5f, 1.5f), Tweaks.DISTORTION_RESX, Tweaks.DISTORTION_RESY, Tweaks.DISTORTION_RESX / 2, Tweaks.DISTORTION_RESY / 2, new Vector2(0.5f, 0.5f));
            Rg32[] pixBuffer = new Rg32[Tweaks.DISTORTION_RESX * Tweaks.DISTORTION_RESY];
            int ix = 0;
            for (int j = 0; j < Tweaks.DISTORTION_RESX; j++) {
                for (int i = 0; i < Tweaks.DISTORTION_RESY; i++) {
                    pixBuffer[ix] = new Rg32(mapData[i, j].X, mapData[i, j].Y);
                    ix++;
                }
            }
            
            euclideanMap.SetData(pixBuffer);
        }

        protected override void UnloadContent() {
            // TODO: Unload any non ContentManager content here
        }

        protected override void Update(GameTime gameTime) {
            float dt = (float) gameTime.ElapsedGameTime.TotalSeconds;

            if (Keyboard.GetState().IsKeyDown(Keys.Escape))
                this.Exit();

            player.Update(dt);
            foreach (Enemy e in enemies) {
                e.Update(dt);
            }


            /*
            for (int i = 0; i < bullets.Count; i++) {
                Bullet bullet = bullets[i];
                bullet.decay -= dt;
                if (bullet.decay > 0) {
                    bullet.pos += dt * metric.lookup(bullet.pos).inverseTransform(bullet.vel);
                    metric.topology.Canonicalize(ref bullet.pos, ref bullet.vel);
                    bullets[i] = bullet;
                }
                else {
                    bullets[i] = bullets[bullets.Count - 1];
                    bullets.RemoveAt(bullets.Count - 1);
                    i--;
                }
            }

            fireTimer -= dt;
            if ((state.Buttons.Y == ButtonState.Pressed || Keyboard.GetState().IsKeyDown(Keys.Space)) && fireTimer <= 0) {
                Bullet bullet = new Bullet();
                bullet.pos = shipPos;
                bullet.vel = shipVel;
                bullet.vel.Normalize();
                bullet.vel *= Tweaks.BULLET_VEL;
                bullet.decay = Tweaks.BULLET_DECAY;
                bullets.Add(bullet);
                fireTimer = Tweaks.BULLET_COOLDOWN;
            }
             */

            base.Update(gameTime);
        }



        protected override void Draw(GameTime gameTime) {
            // Render scene to texture
            graphics.GraphicsDevice.SetRenderTarget(0, renderTarget);
            graphics.GraphicsDevice.Clear(Color.Black);

            effect.CurrentTechnique = effect.Techniques["BasicColorRender"];
            effect.Parameters["xViewMatrix"].SetValue(draw.ortho);
            effect.Begin();
            foreach (EffectPass pass in effect.CurrentTechnique.Passes) {
                pass.Begin();
                graphics.GraphicsDevice.VertexDeclaration = new VertexDeclaration(graphics.GraphicsDevice, VertexPositionColor.VertexElements);
                graphics.GraphicsDevice.DrawUserPrimitives(PrimitiveType.LineList, grid, 0, 32);
                pass.End();
            }
            effect.End();

            Utils.IterateWithDeath(enemies, new Utils.DeathCond<Enemy>(delegate(Enemy e) {
                e.Draw(draw);
                bool death = false;
                foreach (Bullet b in player.Bullets) {
                    if ((b.Position - e.Position).Length() < 0.02f) {
                        death = true;
                        break;
                    }
                }
                return death;
            }));
            foreach (Enemy e in enemies) {
                e.Draw(draw);
            }

            player.Draw(draw);


            // Grab scene texture
            graphics.GraphicsDevice.SetRenderTarget(0, null);
            targetTexture = renderTarget.GetTexture();
            
            VertexPositionTexture[] drawBox = draw.MakeBox(new Vector2(0, 0), new Vector2(1, 1));
            effect.CurrentTechnique = effect.Techniques["DistortionMapRender"];
            effect.Parameters["xScreenTexture"].SetValue(targetTexture);
            effect.Parameters["xDistortionMap"].SetValue(euclideanMap);
            effect.Parameters["xViewMatrix"].SetValue(draw.ortho);
            effect.Begin();
            foreach (EffectPass pass in effect.CurrentTechnique.Passes) {
                pass.Begin();
                graphics.GraphicsDevice.VertexDeclaration = new VertexDeclaration(graphics.GraphicsDevice, VertexPositionTexture.VertexElements);
                graphics.GraphicsDevice.DrawUserPrimitives(PrimitiveType.TriangleFan, drawBox, 0, 2);
                pass.End();
            }
            effect.End();
            
            

            base.Draw(gameTime);
        }
    }
}
