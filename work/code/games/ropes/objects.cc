#include "objects.h"

void ObjectManager::mark(Object* o) {
    if (o->visible_) return;
    o->visible_ = true;
    
    if (gc_tail_) gc_tail_->gc_next_ = o;
    o->gc_next_ = 0;
    gc_tail_ = o;
}

void ObjectManager::sweep() {
    Object* cptr = 0;
    
    gc_tail_ = 0;
    for (set_t::iterator i = oset_.begin(); i != oset_.end(); ++i) {
        (*i)->visible_ = false;
        if ((*i)->visible()) {
            if (!cptr) cptr = *i;
            mark(*i);
        }
    }

    while (cptr) {
        cptr->mark();
        cptr = cptr->gc_next_;
    }

    int cleaned = 0;
    for (set_t::iterator i = oset_.begin(); i != oset_.end(); ) {
        Object* o = *i;
        if (!o->visible_) {
            set_t::iterator next = i;  ++next;
            oset_.erase(i);
            i = next;

            delete o;
            cleaned++;
        }
        else {
            ++i;
        }
    }

    if (cleaned) cout << "Cleaned up " << cleaned << " objects\n";
}

const num Spikey::radius = 0.2;

Spikey::Spikey(vec p, vec f)
    : geom_(p, radius)
{
    body_.set_position(p);
    body_.set_owner(static_cast<void*>(this));
    geom_.attach(&body_);
    body_.set_mass(0.1, radius);

    body_.apply_force(f, p);
}

Rope::Rope(Object* obja, Body* bodya, Object* objb, Body* bodyb)
    : obja_(obja), objb_(objb), selected_(false)
{
    vec apos = bodya->position();
    proxya_.set_position(apos);
    proxya_.set_velocity(bodya->velocity());
    proxya_.set_mass(0.01, 1);
    hingea_ = dJointCreateHinge(WORLD, 0);
    dJointAttach(hingea_, proxya_.body_id(), bodya->body_id());
    dJointSetHingeAxis(hingea_, 0, 0, 1);

    vec bpos = bodyb->position();
    proxyb_.set_position(bpos);
    proxyb_.set_velocity(bodyb->velocity());
    proxyb_.set_mass(0.01, 1);
    hingeb_ = dJointCreateHinge(WORLD, 0);
    dJointAttach(hingeb_, proxyb_.body_id(), bodyb->body_id());
    dJointSetHingeAxis(hingeb_, 0, 0, 1);
    
    rope_ = dJointCreateSlider(WORLD, 0);
    vec axis = bpos - apos;
    dJointAttach(rope_, proxya_.body_id(), proxyb_.body_id());
    dJointSetSliderAxis(rope_, axis.x, axis.y, 0);
    
    dJointSetSliderParam(rope_, dParamLoStop, 0);
    dJointSetSliderParam(rope_, dParamStopCFM, 0.25);
    dJointSetSliderParam(rope_, dParamStopERP, 0.01);

    ext_ = base_ext_ = axis.norm();
}

Rope::~Rope() {
    dJointDestroy(hingea_);
    dJointDestroy(hingeb_);
    dJointDestroy(rope_);
}

void Rope::draw() {
    vec posa = proxya_.position();
    vec posb = proxyb_.position();

    glPushAttrib(GL_LINE_BIT);
        if (selected_) {
            glLineWidth(2.0);
            glColor3d(0,1,0);
        }
        else {
            glColor3d(1,1,1);
        }
        glBegin(GL_LINES);
            glVertex2d(posa.x, posa.y);
            glVertex2d(posb.x, posb.y);
        glEnd();
    glPopAttrib();
}

void Rope::lengthen(num amt) {
    ext_ += amt;
    if (ext_ < 1.2) {  // XXX magic number
        ext_ = 1.2;
    }
    dJointSetSliderParam(rope_, dParamLoStop, base_ext_ - ext_);
}
