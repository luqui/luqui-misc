using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;

namespace DifferentialGeometryWars
{
    class PlayerShip : SpatialObject
    {
        Texture2D shipTexture;
        PlayerIndex player;
        LinkedList<Bullet> bullets;
        float fireCooldown;

        public IEnumerable<Bullet> Bullets { get { return bullets; } }

        public PlayerShip(PlayerIndex inplayer, Metric metric, Vector2 pos)
            : base(pos, new Vector2(0.01f, 0.0f), metric)
        {
            shipTexture = Tweaks.CONTENT.Load<Texture2D>("playerShip");
            player = inplayer;
            bullets = new LinkedList<Bullet>();
            fireCooldown = 0.0f;
        }

        public void Draw(DrawHelper draw) {
            draw.DrawSprite(GetDrawMatrix(), shipTexture, new Vector2(-0.02f, -0.02f), new Vector2(0.02f, 0.02f));
            foreach (Bullet b in bullets) {
                b.Draw(draw);
            }
        }

        public override void Update(float dt) {
            GamePadState state = GamePad.GetState(player);
            float xaxis = state.ThumbSticks.Left.X;
            float theta = -Tweaks.TURN_RESPONSE * dt * xaxis * 7;
            velocity = new Vector2((float) Math.Cos(theta) * velocity.X - (float) Math.Sin(theta) * velocity.Y
                                 , (float) Math.Sin(theta) * velocity.X + (float) Math.Cos(theta) * velocity.Y);
            float len = velocity.Length();
    
            float dlen = state.Triggers.Right - state.Triggers.Left;

            len += Tweaks.ACCEL_RESPONSE * dt * dlen;

            if (len < 0.01) len = 0.01f;
            if (len > Tweaks.MAX_SPEED) len = Tweaks.MAX_SPEED;
            velocity.Normalize();
            velocity *= len;

            fireCooldown -= dt;
            if (fireCooldown <= 0 && state.IsButtonDown(Buttons.Y)) {
                Vector2 vel = velocity;
                vel.Normalize();
                vel *= Tweaks.BULLET_VEL;
                bullets.AddLast(new Bullet(metric, Tweaks.BULLET_DECAY, position, vel));
                fireCooldown = Tweaks.BULLET_COOLDOWN;
            }

            Utils.IterateWithDeath(bullets, new Utils.DeathCond<Bullet>(delegate(Bullet b) {
                b.Update(dt);
                return b.Dead();
            }));

            base.Update(dt);
        }
    }
}
