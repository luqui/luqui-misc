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
        Vector2 shipPos;
        Vector2 shipVel;
        Texture2D euclideanMap;
        Metric metric;

        VertexPositionColor[] grid;

        // Tweaks
        // Metric resolution: higher values allow for more granularity in spacetime bending
        const int METRIC_RESX = 256;
        const int METRIC_RESY = 256;
        // Source resolution: the resolution at which the logical space is rendered
        //   (the thing the distortion filter acts on).   Since the distortion filter
        //   is generally continuous, this is essentially "screen resolution"
        const int SOURCE_RESX = 256;
        const int SOURCE_RESY = 256;
        // Distortion field resolution  (costly to calculate, so is related linearly to startup time)
        const int DISTORTION_RESX = 64;
        const int DISTORTION_RESY = 64;
        // Number of relaxation iterations for finding the distortion map.
        const int DISTORTION_ITERS = 4096;
        // Control responsiveness
        const float TURN_RESPONSE = 0.33f;
        const float ACCEL_RESPONSE = 1.0f;
        const float MAX_SPEED = 0.4f;

        public Game1() {
            graphics = new GraphicsDeviceManager(this);
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
            metric = new Metric(new SphereFundamentalPoly(), METRIC_RESX, METRIC_RESY);
            double theta = 0.6*Math.PI;
            metric.modifyCircle(new Metric.TangentSpace(10*(float)Math.Cos(theta), -10*(float)Math.Sin(theta), 10*(float)Math.Sin(theta), 10*(float)Math.Cos(theta)), new Vector2(0.5f, 0.5f), 0.3f);
            shipPos = new Vector2(0.5f, 0.5f);
            shipVel = new Vector2(0.0f, 0.1f);

            renderTarget = new RenderTarget2D(graphics.GraphicsDevice, SOURCE_RESX, SOURCE_RESY, 0, SurfaceFormat.Color);

            Vector2[,] mapData = metric.getEuclideanMap(new Vector2(-0.5f, -0.5f), new Vector2(1.5f, 1.5f), DISTORTION_RESX, DISTORTION_RESY, DISTORTION_ITERS);
            Rg32[] pixBuffer = new Rg32[DISTORTION_RESX*DISTORTION_RESY];
            int ix = 0;
            for (int j = 0; j < DISTORTION_RESX; j++) {
                for (int i = 0; i < DISTORTION_RESY; i++) {
                    pixBuffer[ix] = new Rg32(mapData[i, j].X, mapData[i, j].Y);
                    ix++;
                }
            }
            
            euclideanMap = new Texture2D(graphics.GraphicsDevice, DISTORTION_RESX, DISTORTION_RESY, 0, TextureUsage.None, SurfaceFormat.Rg32);
            euclideanMap.SetData(pixBuffer);

            {
                Color color = Color.Green;
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

        protected override void UnloadContent() {
            // TODO: Unload any non ContentManager content here
        }

        protected override void Update(GameTime gameTime) {
            // Allows the game to exit
            if (GamePad.GetState(PlayerIndex.One).Buttons.Back == ButtonState.Pressed)
                this.Exit();

            float xaxis = GamePad.GetState(PlayerIndex.One).ThumbSticks.Left.X;
            float theta = -TURN_RESPONSE * (float)gameTime.ElapsedGameTime.TotalSeconds * xaxis * 7;
            shipVel = new Vector2( (float)Math.Cos(theta) * shipVel.X - (float)Math.Sin(theta) * shipVel.Y
                                 , (float)Math.Sin(theta) * shipVel.X + (float)Math.Cos(theta) * shipVel.Y);
            float len = shipVel.Length();
            len += ACCEL_RESPONSE * (float)gameTime.ElapsedGameTime.TotalSeconds * (GamePad.GetState(PlayerIndex.One).Triggers.Right - GamePad.GetState(PlayerIndex.One).Triggers.Left);
            if (len < 0.01) len = 0.01f;
            if (len > MAX_SPEED) len = MAX_SPEED;
            shipVel.Normalize();
            shipVel *= len;

            shipPos += (float) gameTime.ElapsedGameTime.TotalSeconds * metric.lookup(shipPos).inverseTransform(shipVel);
            shipPos = new Vector2(1, 1) - shipPos;
            metric.topology.Canonicalize(ref shipPos, ref shipVel);
            shipPos = new Vector2(1,1)-shipPos;

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
            Matrix trans = Matrix.CreateTranslation(new Vector3(shipPos.X, shipPos.Y, 0.0f));
            Vector2 logVel = metric.lookup(shipPos).inverseTransform(shipVel);
            Matrix rot = Matrix.CreateRotationZ((float)(Math.Atan2(logVel.Y, logVel.X) - Math.PI/2));

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

            
            DrawSprite(rot * trans * ortho, shipTexture, new Vector2(-0.02f, -0.02f), new Vector2(0.02f, 0.02f));

            // Grab scene texture
            graphics.GraphicsDevice.SetRenderTarget(0, null);
            targetTexture = renderTarget.GetTexture();

            // And draw it.
            //DrawSprite(ortho, euclideanMap, new Vector2(0, 0), new Vector2(1, 1));
            //DrawSprite(ortho, targetTexture, new Vector2(0, 0), new Vector2(1, 1));
            
            
            
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
