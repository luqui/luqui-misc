#ifndef __FLUIDGRID_H__
#define __FLUIDGRID_H__

#include "vec.h"


float clamp(float x, float lo, float hi) {
	if (x <= lo) return lo;
	if (x >= hi) return hi;
	return x;
}

class FluidUtils {
public:
	struct Boundary {
		Boundary() : full(false) { }
		vec normal;
		bool full;
	};
	
	typedef float Scr[W][H];
	typedef Boundary Bound[W][H];

	enum BoundComputation { NONE, UNORM, VNORM };

#   define INBOUND_LOOP(i,j) for (int i = 0; i < W; i++) for (int j = 0; j < H; j++)

	static void clear(Scr x) {
		INBOUND_LOOP(i,j) {
			x[i][j] = 0;
		}
	}

	static void set_boundary(BoundComputation comp, Bound bound, Scr x, int i, int j) {
		x[i][j] = 0;
	}
	
	static void diffuse(BoundComputation comp, Bound bound, Scr x, Scr x0, float diffusion) {
		float da = DT * diffusion * (W-2)*(H-2);

		for (int k = 0; k < 20; k++) {  // XXX 20?
			INBOUND_LOOP(i,j) {
				if (bound[i][j].full) {
					set_boundary(comp, bound, x, i, j);
				}
				else {
					x[i][j] = (x0[i][j] + da * (x[i-1][j] + x[i+1][j]
											  + x[i][j-1] + x[i][j+1])) / (1+4*da);
				}
			}
		}
	}

	static void advect(BoundComputation comp, Bound bound, Scr d, Scr d0, Scr u, Scr v) {
		INBOUND_LOOP(i,j) {
			if (bound[i][j].full) {
				set_boundary(comp, bound, d, i, j);
			}
			else {
				float x = i - DT*W*u[i][j];
				float y = j - DT*H*v[i][j];
				int i0 = int(clamp(x, 0.5, W-1.5));
				int i1 = i0+1;
				int j0 = int(clamp(y, 0.5, H-1.5));
				int j1 = j0+1;
				float s1 = x - i0;  float s0 = 1 - s1;
				float t1 = y - j0;  float t0 = 1 - t1;
				d[i][j] = s0*(t0*d0[i0][j0] + t1*d0[i0][j1])
						+ s1*(t0*d0[i1][j0] + t1*d0[i1][j1]);
			}
		}
	}

	static void project(Bound bound, Scr u, Scr v, Scr p, Scr div) {
		float hx = 1.0/W;
		float hy = 1.0/H;

		INBOUND_LOOP(i,j) {
			if (bound[i][j].full) {
				set_boundary(NONE, bound, div, i, j);
			}
			else {
				div[i][j] = -0.5 *( hx * (u[i+1][j] - u[i-1][j])
								  + hy * (v[i][j+1] - v[i][j-1]));
			}
			p[i][j] = 0;
		}

		for (int k = 0; k < 20; k++) {  // XXX 20?
			INBOUND_LOOP(i,j) {
				if (bound[i][j].full) {
					set_boundary(NONE, bound, p, i, j);
				}
				else {
					p[i][j] = (div[i][j] + p[i-1][j] + p[i+1][j]
									     + p[i][j-1] + p[i][j+1]) / 4.0;
				}
			}
		}

		INBOUND_LOOP(i,j) {
			if (bound[i][j].full) {
				set_boundary(UNORM, bound, u, i, j);
				set_boundary(VNORM, bound, v, i, j);
			}
			else {
				u[i][j] -= 0.5 * (p[i+1][j] - p[i-1][j]) / hx;
				v[i][j] -= 0.5 * (p[i][j+1] - p[i][j-1]) / hy;
			}
		}
	}

#   undef INBOUND_LOOP
};

class FluidGrid : private FluidUtils {
public:
	typedef FluidUtils::Bound Bound;
	typedef FluidUtils::Scr Scr;
	
	FluidGrid(vec ll, vec ur, float viscosity)
		: ll_(ll), ur_(ur), viscosity_(viscosity)
	{
		clear(U_);
		clear(V_);
		clear(U_back_);
		clear(V_back_);
	}
		

	bool in_range(vec v) const {
		return ll_.x <= v.x && v.x < ur_.x
			&& ll_.y <= v.y && v.y < ur_.y;
	}
	
	void add_velocity(vec x, vec v) {
		const int xx = ix_x(x.x), yy = ix_y(x.y);
		U_[xx][yy] += DT * v.x;
		V_[xx][yy] += DT * v.y;
	}

	vec get_velocity(vec x) const {
		const int xx = ix_x(x.x), yy = ix_y(x.y);
		return vec(U_[xx][yy], V_[xx][yy]);
	}

	void step_velocity(Bound bound) {
		internal_step(bound, U_, V_, U_back_, V_back_);
	}

protected:
	void internal_step(Bound bound, Scr u, Scr v, Scr u0, Scr v0) {
		diffuse(FluidUtils::UNORM, bound, u0, u, viscosity_);
		diffuse(FluidUtils::VNORM, bound, v0, v, viscosity_);
		project(bound, u0, v0, u, v);
		advect(FluidUtils::UNORM, bound, u, u0, u0, v0);
		advect(FluidUtils::VNORM, bound, v, v0, u0, v0);
		project(bound, u, v, u0, v0);
	}
	
	bool in_range_i(int x, int y) const {
		return 0 <= x && x < W && 0 <= y && y < H;
	}

	int ix_x(float x) const {
		return int((x - ll_.x) / (ur_.x - ll_.x) * W);
	}

	int ix_y(float y) const {
		return int((y - ll_.y) / (ur_.y - ll_.y) * H);
	}

	const vec ll_, ur_;
	float viscosity_;
	
	Scr U_, V_;  // x- and y-components of velocity
	Scr U_back_, V_back_;
};


class DensityGrid : private FluidUtils {
public:
	typedef FluidUtils::Bound Bound;
	typedef FluidUtils::Scr Scr;

	DensityGrid(vec ll, vec ur, float diffusion) 
		: ll_(ll), ur_(ur), diffusion_(diffusion)
	{
		clear(D_);
		clear(D_back_);
	}
	
	bool in_range(vec v) const {
		return ll_.x <= v.x && v.x < ur_.x
			&& ll_.y <= v.y && v.y < ur_.y;
	}

	void add_density(vec x, float amt) {
		const int xx = ix_x(x.x), yy = ix_y(x.y);
		D_[xx][yy] += DT * amt;
	}

	float get_density(vec x) const {
		const int xx = ix_x(x.x), yy = ix_y(x.y);
		return D_[xx][yy];
	}

	void step_density(Bound bound, Scr u, Scr v) {
		diffuse(FluidUtils::NONE, bound, D_back_, D_, diffusion_);
		advect(FluidUtils::NONE, bound, D_, D_back_, u, v);
	}

	float get_density_direct(int x, int y) const {
		return D_[x][y];
	}
	
protected:
	int ix_x(float x) const {
		return int((x - ll_.x) / (ur_.x - ll_.x) * W);
	}

	int ix_y(float y) const {
		return int((y - ll_.y) / (ur_.y - ll_.y) * H);
	}

	const vec ll_, ur_;
	float diffusion_;

	Scr D_;
	Scr D_back_;
};

class FluidDensityGrid : public FluidGrid, public DensityGrid {
public:
	typedef FluidGrid::Bound Bound;
	typedef FluidGrid::Scr Scr;
	
	FluidDensityGrid(vec ll, vec ur, float diffusion, float viscosity)
		: FluidGrid(ll, ur, viscosity), DensityGrid(ll, ur, diffusion)
	{ }

	void step_density(Bound bound) {
		DensityGrid::step_density(bound, FluidGrid::U_, FluidGrid::V_);
	}

	void step_velocity(Bound bound) {
		FluidGrid::step_velocity(bound);
	}
};

#endif
