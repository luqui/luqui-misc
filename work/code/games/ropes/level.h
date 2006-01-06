#ifndef __LEVEL_H__
#define __LEVEL_H__

#include "common.h"

class Player;
class ObjectManager;

class Level {
public:
    Level()
        : left(FP_NAN), right(FP_NAN), top(FP_NAN), bottom(FP_NAN),
          p1(0), p2(0), player(0), manager(0),
          world(0), collide_space(0), contact_joints(0) 
    { }
    ~Level();
    
    void load_level(string file);

    void step();
    void draw();

    num left, right, top, bottom;
    Player* p1;
    Player* p2;
    Player* player;

    ObjectManager* manager;
    
    dWorldID world;
    
    dSpaceID collide_space;
    dJointGroupID contact_joints;

private:
    void set_view();
    
    int stepct_;
};

extern Level* LEVEL;

#endif
