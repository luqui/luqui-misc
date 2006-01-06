#include "level.h"
#include "objects.h"
#include "player.h"
#include <fstream>

Level* LEVEL = 0;

static void literal(istream& fin, string lit) {
    string tmp;
    fin >> tmp;
    if (tmp != lit) DIE("Syntax error: expecting " + lit + "; got " + tmp);
}

struct BoxDef {
    vec ll, ur;
};    

Level::~Level() {
    delete manager;
}

void Level::load_level(string file)
{
    ifstream fin(file.c_str());

    cout << "Reading " << file << endl;
    
    literal(fin, "left");
    fin >> left;
    literal(fin, "bottom");
    fin >> bottom;
    literal(fin, "right");
    fin >> right;
    literal(fin, "top");
    fin >> top;

    vec p1pos, p2pos;
    literal(fin, "p1");
    fin >> p1pos.x >> p1pos.y;
    literal(fin, "p2");
    fin >> p2pos.x >> p2pos.y;

    num gravity;
    literal(fin, "gravity");
    fin >> gravity;
    
    int boxes;
    literal(fin, "boxes");
    fin >> boxes;
    
    list<BoxDef> boxen;
    for (int i = 0; i < boxes; i++) {
        BoxDef bx;
        literal(fin, "box");
        fin >> bx.ll.x >> bx.ll.y >> bx.ur.x >> bx.ur.y;
        boxen.push_back(bx);
    }

    cout << "Building level\n";
    
    world = dWorldCreate();
    dWorldSetGravity(world, 0, -gravity, 0);
    collide_space = dSimpleSpaceCreate(0);
    contact_joints = dJointGroupCreate(0);
    
    manager = new ObjectManager;
    p1 = new Player(p1pos);
    manager->add(p1);
    p2 = new Player(p2pos);
    manager->add(p2);

    for (list<BoxDef>::iterator i = boxen.begin(); i != boxen.end(); ++i) {
        manager->add(new Wall(i->ll, i->ur));
    }

    set_view();

    player = p1;
    stepct_ = 5*int(1/STEP);
}

void Level::set_view()
{
    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluOrtho2D(left, right, bottom, top);
    glMatrixMode(GL_MODELVIEW);
}

void Level::step()
{
    if (--stepct_ == 0) {
        manager->sweep();
        stepct_ = 5*int(1/STEP);
    }

    manager->step();
    collide();
    dWorldQuickStep(world, STEP);
    dJointGroupEmpty(contact_joints);
}

void Level::draw()
{
    manager->draw();
}
