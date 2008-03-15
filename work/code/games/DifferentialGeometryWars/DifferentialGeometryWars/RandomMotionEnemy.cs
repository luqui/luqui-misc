using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;

namespace DifferentialGeometryWars
{
    class RandomMotionEnemy : Enemy
    {
        Texture2D enemyTexture;

        public RandomMotionEnemy(Metric metric, Vector2 pos)
            : base(metric, pos) {
            enemyTexture = Tweaks.CONTENT.Load<Texture2D>("zetaEnemy");
        }

        public override void Update(float dt) {
            velocity += 0.1f*dt*new Vector2((float)(2*Tweaks.RAND.NextDouble()-1), (float)(2*Tweaks.RAND.NextDouble()-1));
            if (velocity.Length() > 1) {
                velocity.Normalize();
            }

            base.Update(dt);
        }

        public override void Draw(DrawHelper draw) {
            draw.DrawSprite(GetDrawMatrix(), enemyTexture, new Vector2(-0.02f, -0.02f), new Vector2(0.02f, 0.02f));
        }
    }
}
