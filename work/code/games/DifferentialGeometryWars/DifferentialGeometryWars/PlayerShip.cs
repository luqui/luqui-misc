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
        float turretAngle;

        public IEnumerable<Bullet> Bullets { get { return bullets; } }

        public PlayerShip(PlayerIndex inplayer, Metric metric, Vector2 pos)
            : base(pos, new Vector2(0.01f, 0.0f), metric)
        {
            shipTexture = Tweaks.CONTENT.Load<Texture2D>("playerShip");
            player = inplayer;
            bullets = new LinkedList<Bullet>();
            turretAngle = 0.0f;
            fireCooldown = 0.0f;
        }

        public void Draw(DrawHelper draw) {
            draw.DrawSprite(GetDrawMatrix(), shipTexture, new Vector2(-0.02f, -0.02f), new Vector2(0.02f, 0.02f));
            draw.DrawLine(GetVectorMatrix(new Vector2((float) Math.Cos(turretAngle), (float) Math.Sin(turretAngle))) 
                             * GetTranslationMatrix() * draw.ortho
                         , new Vector2(), new Vector2(0.0f, 0.04f), Color.LightPink);

            foreach (Bullet b in bullets) {
                b.Draw(draw);
            }
        }

        public override void Update(float dt) {
            GamePadState state = GamePad.GetState(player);
            KeyboardState keyState = Keyboard.GetState(player);
            float xaxis = state.ThumbSticks.Left.X;
            if (keyState.IsKeyDown(Keys.A)) { xaxis = -1; }
            else if (keyState.IsKeyDown(Keys.D)) { xaxis = 1; }

            float theta = -Tweaks.TURN_RESPONSE * dt * xaxis;

            velocity = new Vector2((float) Math.Cos(theta) * velocity.X - (float) Math.Sin(theta) * velocity.Y
                                 , (float) Math.Sin(theta) * velocity.X + (float) Math.Cos(theta) * velocity.Y);
            float len = velocity.Length();
    
            float dlen = state.Triggers.Right - state.Triggers.Left;
            if (keyState.IsKeyDown(Keys.W)) { dlen = 1; }
            else if (keyState.IsKeyDown(Keys.S)) { dlen = -1; }

            len += Tweaks.ACCEL_RESPONSE * dt * dlen;

            if (len < 0.01) len = 0.01f;
            if (len > Tweaks.MAX_SPEED) len = Tweaks.MAX_SPEED;
            velocity.Normalize();
            velocity *= len;
            
            fireCooldown -= dt;
            float turaxis = state.ThumbSticks.Right.X;
            if (keyState.IsKeyDown(Keys.Left)) { turaxis = -1; }
            else if (keyState.IsKeyDown(Keys.Right)) { turaxis = 1; }
            turretAngle -= Tweaks.TURRET_RESPONSE * dt * turaxis;

            if (fireCooldown <= 0 && (state.IsButtonDown(Buttons.RightShoulder) || keyState.IsKeyDown(Keys.Space))) {
                Vector2 vel = new Vector2((float) Math.Cos(turretAngle), (float) Math.Sin(turretAngle));
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
