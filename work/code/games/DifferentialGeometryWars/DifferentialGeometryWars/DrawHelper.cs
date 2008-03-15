using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace DifferentialGeometryWars
{
    class DrawHelper
    {
        GraphicsDeviceManager graphics;
        Effect effect;
        EffectTechnique techniqueBasicTexturedRender;
        EffectParameter paramViewMatrix;
        EffectParameter paramBoundTexture;
        public Matrix ortho;

        public DrawHelper(GraphicsDeviceManager ingraphics, Effect ineffect) {
            graphics = ingraphics;
            effect = ineffect;
            techniqueBasicTexturedRender = effect.Techniques["BasicTexturedRender"];
            paramBoundTexture = effect.Parameters["xBoundTexture"];
            paramViewMatrix = effect.Parameters["xViewMatrix"];
            ortho = Matrix.CreateOrthographicOffCenter(0, 1, 0, 1, -1, 1);
        }


        public void DrawSprite(Matrix trans, Texture tex, Vector2 ll, Vector2 ur) {
            VertexPositionTexture[] drawBox = MakeBox(ll, ur);

            effect.CurrentTechnique = techniqueBasicTexturedRender;
            paramViewMatrix.SetValue(trans * ortho);
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

        public VertexPositionTexture[] MakeBox(Vector2 ll, Vector2 ur) {
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

    }
}
