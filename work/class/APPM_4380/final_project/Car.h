#ifndef __CAR_H__
#define __CAR_H__

#include <soy/vec2.h>
#include "Road.h"

class Car {
public:
	Car(Road* road, vec2 pos) 
		: road_(road), pos_(pos), comfort_(0), max_accel_(0),
		  dead_(false), time_(0)
	{
		road_->insert_car(this);
	}

	~Car() {
		if (road_) {
			road_->delete_car(this);
		}
	}

	vec2 get_position() const {
		return pos_;
	}

	double get_time() const {
		return time_;
	}

	void set_comfort_distance(double comfort) {
		comfort_ = comfort;
	}

	void set_max_accel(double accel) {
		max_accel_ = accel;
	}

	bool dead() const {
		return dead_;
	}

	void step() {
		if (dead_) return;
		time_ += DT;
		
		const Car* next = road_->get_next_car(this);
		if (!next || (pos_ - next->get_position()).norm() - 1 >= comfort_ * vel_.norm()) {
			if ((vel_ + max_accel_ * DT * road_->get_direction()).norm() < road_->get_speed_limit()) {
				vel_ += max_accel_ * DT * road_->get_direction();
			}
			else {
				vel_ = road_->get_speed_limit() * road_->get_direction();
			}
		}
		else {
			vel_ = ~road_->get_direction() * ((pos_ - next->get_position()).norm() - 1) / comfort_;
		}

		if ((road_->get_dest()->get_position() - pos_) * road_->get_direction() < 0) {
			road_->get_dest()->pass_under();
			road_->delete_car(this);
			road_ = road_->get_dest()->get_road(road_->get_direction_id());
			if (road_) {
				road_->insert_car(this);
			}
			else {
				dead_ = true;
			}
		}
		else if (!road_->get_dest()->green(opposite_dir(road_->get_direction_id()), road_->get_direction_id())) {
			// x = v^2/2a  (distance it takes to stop)
			double lightdist = (road_->get_dest()->get_position() - 1*road_->get_direction() - pos_) * road_->get_direction();
			if (lightdist < vel_.norm2() / (2*max_accel_)) {
				double target;
				if (lightdist < 0) {
					target = 0;
				}
				else {
					target = sqrt(2 * max_accel_ * lightdist);
				}

				// if the light suddenly turns, cars won't come to
				// a screeching halt, but rather continue through
				if (fabs(vel_.norm() - target) < 5 * max_accel_ * DT) {
					vel_ = road_->get_direction() * target;
				}
			}
		}

		pos_ += DT * vel_;
	}

	void draw() const {
		if (dead_) return;
		
		glPushMatrix();
		glTranslatef(pos_.x, pos_.y, 0);
		glColor3f(1,0,0);
		glBegin(GL_QUADS);
			glVertex2f(-0.5, -0.5);
			glVertex2f( 0.5, -0.5);
			glVertex2f( 0.5,  0.5);
			glVertex2f(-0.5,  0.5);
		glEnd();
		glColor3f(0,0,0);
		glBegin(GL_LINE_LOOP);
			glVertex2f(-0.5, -0.5);
			glVertex2f( 0.5, -0.5);
			glVertex2f( 0.5,  0.5);
			glVertex2f(-0.5,  0.5);
		glEnd();
		glPopMatrix();
	}
private:
	Road* road_;
	vec2 pos_;
	vec2 vel_;
	double comfort_;    // units: s
	double max_accel_;  // units: m/s^2
	bool dead_;
	double time_;
};

#endif
