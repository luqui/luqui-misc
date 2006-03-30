#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>

#include <cmath>
#include <list>
#include <iostream>

using std::list;

struct Node {
	Node(float theta, float length) : theta(theta), dtheta(0), length(length),  dlength(0),
									  light(0), alllight(0)
	{ }
	~Node() {
		for (children_t::iterator i = children.begin(); i != children.end(); ++i) {
			delete *i;
		}
	}
	
	float theta, dtheta;
	float length, dlength;
	float light;
	float alllight;
	typedef list<Node*> children_t;
	children_t children;

	template <class I>
	void traverse(I& f, float x, float y, float th) {
		float nth = th + theta;
		float nx = x + length * sin(nth);
		float ny = y + length * cos(nth);
		f(this,x,y,nx,ny);

		for (children_t::const_iterator i = children.begin(); i != children.end(); ++i) {
			(*i)->traverse(f,nx,ny,nth);
		}
	}

	float compute_all_light() {
		alllight = light;
		for (children_t::iterator i = children.begin(); i != children.end(); ++i) {
			alllight += (*i)->compute_all_light();
		}
		return alllight;
	}

	void step() {
		theta += dtheta;
		length += dlength;
		dtheta = 0;
		dlength = 0;
		for (children_t::iterator i = children.begin(); i != children.end(); ++i) {
			(*i)->step();
		}
	}
};

void init_sdl() {
	SDL_Init(SDL_INIT_VIDEO);
	
	SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
	SDL_SetVideoMode(800, 600, 0, SDL_OPENGL);

	glMatrixMode(GL_PROJECTION);
		glLoadIdentity();
		gluOrtho2D(-4, 4, 0, 6);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

Node* make_tree(float theta, float length, int children, int depth) {
	Node* cur = new Node(theta, length);
	
	if (depth > 0) {
		for (int i = 0; i < children; i++) {
			cur->children.push_back(make_tree(M_PI/8 * (2*i-1), 0.7*length, children, depth-1));
		}
	}
	return cur;
}

void events() {
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}
	}
}

struct DrawTraverser {
	void operator () (Node* n, float x, float y, float nx, float ny) {
		float l = 0.3 + 3 * n->light;
		glColor3f(l,l,l);
		glBegin(GL_LINES);
			glVertex2f(x,y);
			glVertex2f(nx,ny);
		glEnd();
	}
};

struct NodeSegment {
	NodeSegment(float x0, float y0, float x1, float y1, Node* node) 
		: x0(x0), y0(y0), x1(x1), y1(y1), node(node)
	{ }
	float x0,y0,x1,y1;
	Node* node;
};

struct NodeCollector {
	typedef list<NodeSegment> segs_t;
	segs_t segs;

	void operator () (Node* node, float x, float y, float nx, float ny) {
		segs.push_back(NodeSegment(x,y,nx,ny,node));
	}
};

struct AllNodesCollector {
	typedef list<Node*> nodes_t;
	nodes_t nodes;

	void operator() (Node* node, float x, float y, float nx, float ny) {
		nodes.push_back(node);
	}
};

// returns the square distance from (lx0,ly0) to the intersection point
// if there is no intersection, then returns a negative number (XXX not elegant)
float seg_line_intersect(float rx0, float ry0, float rx1, float ry1,
						 float lx0, float ly0, float lx1, float ly1)
{
	float rt = ((ly0 - ly1) * rx0 + lx0 * (ly1 - ry0) + lx1 * (ry0 - ly0)) /
			   ((ly0 - ly1) * (rx0 - rx1) - (lx0 - lx1) * (ry0-ry1));
	if (0 <= rt && rt <= 1) {
		float intx = rx0 + (rx1 - rx0) * rt;
		float inty = ry0 + (ry1 - ry0) * rt;

		return ((intx - lx0)*(intx - lx0) + (inty - ly0)*(inty - ly0));
	}
	else {
		return -1;
	}
}

void compute_light(const list<NodeSegment>& segs, float sunx, float suny) {
	for (list<NodeSegment>::const_iterator i = segs.begin(); i != segs.end(); ++i) {
		float ix0 = (i->x0 + i->x1)/2;
		float iy0 = (i->y0 + i->y1)/2;
		if (ix0 < -4 || ix0 > 4 || iy0 < 0 || iy0 > 6) {
			i->node->light = 0;
		}
		else {
			float potlight = 1;
			float dist2 = (ix0 - sunx) * (ix0 - sunx) + (iy0 - suny) * (iy0 - suny);
			for (list<NodeSegment>::const_iterator j = segs.begin(); j != segs.end(); ++j) {
				if (i == j) continue;
				float intersect = seg_line_intersect(
									j->x0, j->y0, j->x1, j->y1,
									sunx, suny, ix0, iy0);
				if (0 < intersect && intersect < dist2) {
					potlight /= 10;
				}
			}
			float normx = iy0 - suny;
			float normy = -(ix0 - sunx);
			float normnorm = sqrt(normx*normx + normy*normy);
			normx /= normnorm;
			normy /= normnorm;
			
			i->node->light = sqrt(fabs((i->x1 - i->x0) * normx + (i->y1 - i->y0) * normy)) * potlight;
		}
	}
}

list<Node*> ALLNODES;

void step(Node* head) {	
	static list<Node*>::iterator curnode = ALLNODES.begin();
	
	int x, y;
	SDL_GetMouseState(&x, &y);
	float xx = 8.0 * x / 800.0 - 4.0;
	float yy = 6.0 * (1.0 - y / 600.0);

	{
		NodeCollector cp;
		head->traverse(cp, 0, 0, 0);
		compute_light(cp.segs, xx,yy);
	}
	float light0 = head->compute_all_light();
	std::cout << light0 << "\n";
	
	curnode = ALLNODES.begin();
	while (curnode != ALLNODES.end()) {
		{
			(*curnode)->theta += 0.05;
			{
				NodeCollector cp;
				head->traverse(cp, 0, 0, 0);
				compute_light(cp.segs, xx,yy);
			}
			float lighti = head->compute_all_light();
			(*curnode)->dtheta = (rand() % 100 == 42 ? 0.1 : 0.005)*(lighti - light0);
			(*curnode)->theta -= 0.05;
		}

		{
			(*curnode)->length += 0.05;
			{
				NodeCollector cp;
				head->traverse(cp, 0, 0, 0);
				compute_light(cp.segs, xx,yy);
			}
			float lighti = head->compute_all_light();
			(*curnode)->dlength = 0.05*(lighti - light0);
			(*curnode)->length -= 0.05;
		}
		++curnode;
	}

	head->step();
}


int main() {
	init_sdl();

	Node* head = make_tree(0, 1, 2, 6);
	AllNodesCollector anc;
	head->traverse(anc, 0, 0, 0);
	ALLNODES = anc.nodes;

	while (true) {
		events();
		glClear(GL_COLOR_BUFFER_BIT);
		DrawTraverser d;
		head->traverse(d, 0, 0, 0);
		step(head);
		SDL_GL_SwapBuffers();
	}
}
