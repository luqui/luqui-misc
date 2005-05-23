#ifndef __BALL_H__
#define __BALL_H__

#include <cmath>

class Ball
{
public:
    Ball() : momentum_(150), mass_(2), ypos_(0) { }

    float mass()      const { return mass_; }
    float velocity()  const { return momentum_ / mass_; }
    float size()      const { return 1.3 * std::sqrt(mass_); }
    float momentum()  const { return momentum_; }
    
    void move(float dir)         { ypos_ += STEP * dir; }
    void grow(float dir)         { mass_ += STEP * dir; }
    void add_momentum(float dir) { momentum_ += STEP * dir; }
private:
    float momentum_;
    float mass_;
    float ypos_;
};

#endif
