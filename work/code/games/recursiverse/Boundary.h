#ifndef __BOUNDARY_H__
#define __BOUNDARY_H__

struct EnemyBall {
    EnemyBall(float center, float radius) 
        : center(center), radius(radius), next(0) { }
    
    float center;
    float radius;
    EnemyBall* next;
};

struct BoundaryFrame {
    BoundaryFrame(float center, float radius) 
        : center(center), radius(radius), next(0) { }
    
    float center;
    float radius;
    BoundaryFrame* next;
};

struct XFrame {
    XFrame(float x) : x(x) { }
    
    EnemyBall* enemies;
    BoundaryFrame* boundary;
    float x;
};

static const int buffer_length = 500;

class Boundary {
public:
private:
};

#endif
