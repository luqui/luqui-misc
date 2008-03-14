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
        EffectTechnique techniqueBasicTexturedRender;
        EffectParameter paramViewMatrix;
        EffectParameter paramBoundTexture;
        RenderTarget2D renderTarget;
        Texture2D targetTexture;

        Texture2D shipTexture;
        Texture2D bulletTexture;
        Vector2 shipPos;
        Vector2 shipVel;
        Texture2D euclideanMap;
        Metric metric;

        VertexPositionColor[] grid;

        struct Bullet {
            public Vector2 pos;
            public Vector2 vel;
            public float decay;
        };
        List<Bullet> bullets;
        float fireTimer;

        // Tweaks
        // Metric resolution: higher values allow for more granularity in spacetime bending
        const int METRIC_RESX = 512;
        const int METRIC_RESY = 512;
        // Source resolution: the resolution at which the logical space is rendered
        //   (the thing the distortion filter acts on).   Since the distortion filter
        //   is generally continuous, this is essentially "screen resolution"
        const int SOURCE_RESX = 512;
        const int SOURCE_RESY = 512;
        // Distortion field resolution  (costly to calculate, so is related linearly to startup time)
        const int DISTORTION_RESX = 512;
        const int DISTORTION_RESY = 512;
        // Control responsiveness
        const float TURN_RESPONSE = 0.33f;
        const float ACCEL_RESPONSE = 1.0f;
        const float MAX_SPEED = 0.4f;
        // Bullets
        const float BULLET_VEL = 0.6f;
        const float BULLET_COOLDOWN = 0.05f;
        const float BULLET_DECAY = 2.0f;

        public Game1() {
            graphics = new GraphicsDeviceManager(this);
            graphics.PreferredBackBufferWidth = 1440;
            graphics.PreferredBackBufferHeight = 900;
            graphics.IsFullScreen = true;
            Content.RootDirectory = "Content";
        }

        protected override void Initialize() {
            // TODO: Add your initialization logic here

            base.Initialize();
        }


        protected override void LoadContent() {
            effect = Content.Load<Effect>("Effects");
            techniqueBasicTexturedRender = effect.Techniques["BasicTexturedRender"];
            paramBoundTexture = effect.Parameters["xBoundTexture"];
            paramViewMatrix = effect.Parameters["xViewMatrix"];

            shipTexture = Content.Load<Texture2D>("playerShip");
            bulletTexture = Content.Load<Texture2D>("bullet");
            metric = new Metric(new SphereFundamentalPoly(), METRIC_RESX, METRIC_RESY);
            shipPos = new Vector2(0.5f, 0.5f);
            shipVel = new Vector2(0.0f, 0.1f);
            bullets = new List<Bullet>();
            fireTimer = 0;

            renderTarget = new RenderTarget2D(graphics.GraphicsDevice, SOURCE_RESX, SOURCE_RESY, 0, SurfaceFormat.Color);
            double theta = Math.PI / 2;
            //metric.modifyCircle(new Metric.TangentSpace((float)Math.Cos(theta), -(float)Math.Sin(theta), (float)Math.Sin(theta), (float)Math.Cos(theta)), new Vector2(1.0f, 0.0f), 0.25f);
            metric.modifyCircle(new Metric.TangentSpace(1.0f, 0.0f, -1.0f, 1.0f), new Vector2(0.7f, 0.7f), 0.3f);
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
            euclideanMap = new Texture2D(graphics.GraphicsDevice, DISTORTION_RESX, DISTORTION_RESY, 0, TextureUsage.None, SurfaceFormat.Rg32);
            Vector2[,] mapData = metric.getEuclideanMap(new Vector2(-0.5f, -0.5f), new Vector2(1.5f, 1.5f), DISTORTION_RESX, DISTORTION_RESY, DISTORTION_RESX / 2, DISTORTION_RESY / 2, new Vector2(0.5f, 0.5f));
            Rg32[] pixBuffer = new Rg32[DISTORTION_RESX * DISTORTION_RESY];
            int ix = 0;
            for (int j = 0; j < DISTORTION_RESX; j++) {
                for (int i = 0; i < DISTORTION_RESY; i++) {
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
            float dt = (float)gameTime.ElapsedGameTime.TotalSeconds;
            GamePadState state = GamePad.GetState(PlayerIndex.One);

            if (state.Buttons.Back == ButtonState.Pressed)
                this.Exit();

            float xaxis = state.ThumbSticks.Left.X;
            float theta = -TURN_RESPONSE * dt * xaxis * 7;
            shipVel = new Vector2( (float)Math.Cos(theta) * shipVel.X - (float)Math.Sin(theta) * shipVel.Y
                                 , (float)Math.Sin(theta) * shipVel.X + (float)Math.Cos(theta) * shipVel.Y);
            float len = shipVel.Length();
            len += ACCEL_RESPONSE * dt * (state.Triggers.Right - state.Triggers.Left);
            if (len < 0.01) len = 0.01f;
            if (len > MAX_SPEED) len = MAX_SPEED;
            shipVel.Normalize();
            shipVel *= len;

            shipPos += dt * metric.lookup(shipPos).inverseTransform(shipVel);
            metric.topology.Canonicalize(ref shipPos, ref shipVel);

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
            if (state.Buttons.Y == ButtonState.Pressed && fireTimer <= 0) {
                Bullet bullet = new Bullet();
                bullet.pos = shipPos;
                bullet.vel = shipVel;
                bullet.vel.Normalize();
                bullet.vel *= BULLET_VEL;
                bullet.decay = BULLET_DECAY;
                bullets.Add(bullet);
                fireTimer = BULLET_COOLDOWN;
            }

            base.Update(gameTime);
        }

        private VertexPositionTexture[] makeBox(Vector2 ll, Vector2 ur) {
            VertexPositionTexture[] drawBox = new VertexPositionTexture[4];
            drawBox[0].Position = new Vector3(ll.X, ll.Y, 0.0f);
            drawBox[0].TextureCoordinate = new Vector2(0.0f, 1.0f);
            drawBox[1].Position = new Vector3(ll.X, ur.Y, 0.0f);
            drawBox[1].TextureCoordinate = new Vector2(0.0f, 0.0f);
            drawBox[2].Position = new Vector3(ur.X, ur.Y, 0.0f);
            drawBox[2].TextureCoordinate = new Vector2(1.0f, 0.0f);
            drawBox[3].Position = new Vector3(ur.X, ll.Y, 0.0f);
            drawBox[3].TextureCoordinate = new Vector2(1.0f, 1.0f);
            return drawBox;
        }

        private void DrawSprite(Matrix trans, Texture tex, Vector2 ll, Vector2 ur) {
            VertexPositionTexture[] drawBox = makeBox(ll, ur);

            effect.CurrentTechnique = techniqueBasicTexturedRender;
            paramViewMatrix.SetValue(trans);
            paramBoundTexture.SetValue(tex);
            effect.Begin();
            foreach (EffectPass pass in effect.CurrentTechnique.Passes) {
                pass.Begin();
                graphics.GraphicsDevice.VertexDeclaration = new VertexDeclaration(graphics.GraphicsDevice, VertexPositionTexture.VertexElements);
                graphics.GraphicsDevice.DrawUserPrimitives(PrimitiveType.TriangleFan, drawBox, 0, 2);
                pass.End();
            }
            effect.End();
        }

        protected override void Draw(GameTime gameTime) {
            // Render scene to texture
            graphics.GraphicsDevice.SetRenderTarget(0, renderTarget);
            graphics.GraphicsDevice.Clear(Color.Black);

            Matrix ortho = Matrix.CreateOrthographicOffCenter(0, 1, 0, 1, -1, 1);


            effect.CurrentTechnique = effect.Techniques["BasicColorRender"];
            effect.Parameters["xViewMatrix"].SetValue(ortho);
            effect.Begin();
            foreach (EffectPass pass in effect.CurrentTechnique.Passes) {
                pass.Begin();
                graphics.GraphicsDevice.VertexDeclaration = new VertexDeclaration(graphics.GraphicsDevice, VertexPositionColor.VertexElements);
                graphics.GraphicsDevice.DrawUserPrimitives(PrimitiveType.LineList, grid, 0, 32);
                pass.End();
            }
            effect.End();

            {
                Matrix trans = Matrix.CreateTranslation(new Vector3(shipPos.X, shipPos.Y, 0.0f));
                Vector2 logVel = metric.lookup(shipPos).inverseTransform(shipVel);
                Matrix rot = Matrix.CreateRotationZ((float)(Math.Atan2(logVel.Y, logVel.X) - Math.PI/2));

                DrawSprite(rot * trans * ortho, shipTexture, new Vector2(-0.02f, -0.02f), new Vector2(0.02f, 0.02f));
            }

            foreach (Bullet bullet in bullets) {
                Matrix trans = Matrix.CreateTranslation(new Vector3(bullet.pos.X, bullet.pos.Y, 0.0f));
                Vector2 logVel = metric.lookup(bullet.pos).inverseTransform(bullet.vel);
                Matrix rot = Matrix.CreateRotationZ((float)(Math.Atan2(logVel.Y, logVel.X) - Math.PI/2));
                DrawSprite(rot * trans * ortho, bulletTexture, new Vector2(-0.005f, -0.005f), new Vector2(0.005f, 0.005f));
            }

            // Grab scene texture
            graphics.GraphicsDevice.SetRenderTarget(0, null);
            targetTexture = renderTarget.GetTexture();
            
            VertexPositionTexture[] drawBox = makeBox(new Vector2(0, 0), new Vector2(1, 1));
            effect.CurrentTechnique = effect.Techniques["DistortionMapRender"];
            effect.Parameters["xScreenTexture"].SetValue(targetTexture);
            effect.Parameters["xDistortionMap"].SetValue(euclideanMap);
            effect.Parameters["xViewMatrix"].SetValue(ortho);
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
