using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace DifferentialGeometryWars
{
    class Bullet : SpatialObject
    {
        Texture2D bulletTexture;
        float timeout;

        public Bullet(Metric metric, float intimeout, Vector2 pos, Vector2 vel)
            : base(pos, vel, metric) {
            bulletTexture = Tweaks.CONTENT.Load<Texture2D>("bullet");
            timeout = intimeout;
        }

        public override void Update(float dt) {
            timeout -= dt;
            base.Update(dt);
        }

        public void Draw(DrawHelper draw) {
            draw.DrawSprite(GetDrawMatrix(), bulletTexture, new Vector2(-0.005f, -0.005f), new Vector2(0.005f, 0.005f));
        }

        public bool Dead() {
            return timeout <= 0;
        }
    }
}
