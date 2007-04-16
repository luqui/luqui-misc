#include <soy/init.h>
#include <list>
#include <GL/gl.h>
#include <GL/glu.h>
#include <memory>
#include <iostream>

const int SIZEX = 19, SIZEY = 19;
const int AIDEPTH = 3;
const int AISEARCH = 2;

SoyInit INIT;

enum Color { NONE, WHITE, BLACK, N_COLORS };
inline Color other_color(Color in) {
    return in == WHITE ? BLACK : WHITE;
}

class Move;

struct BoardExtents {
    int minx, miny, maxx, maxy;

    void expand(int n) {
        minx -= n;
        miny -= n;
        maxx += n;
        maxy += n;
        if (minx < 0) minx = 0;
        if (miny < 0) miny = 0;
        if (maxx > SIZEX-1) maxx = SIZEX-1;
        if (maxy > SIZEY-1) maxy = SIZEY-1;
    }
};

class Board {
public:
    Board() {
        for (int i = 0; i < SIZEX; i++) {
            for (int j = 0; j < SIZEY; j++) {
                board_[i][j] = NONE;
            }
        }
        for (int i = 0; i < N_COLORS; i++) {
            cap_[i] = 0;
        }
    }

    Move* create_move(Color color, int x, int y) const;
    void do_move(const Move* move);
    void undo_move(const Move* move);
    bool in_range(int x, int y) const {
        return 0 <= x && x < SIZEX && 0 <= y && y < SIZEY;
    }
    int captures(Color color) const {
        return cap_[color];
    }
    bool win(Color color) const {
        return captures(color) >= 9;
    }
    Color get_color(int x, int y) const {
        return board_[x][y];
    }

    BoardExtents extents() const {
        BoardExtents e;

        e.minx = SIZEX-1;
        e.miny = SIZEY-1;
        e.maxx = 0;
        e.maxy = 0;
        
        for (int i = 0; i < SIZEX; i++) {
            for (int j = 0; j < SIZEY; j++) {
                if (board_[i][j]) {
                    if (i < e.minx) e.minx = i;
                    if (j < e.miny) e.miny = j;
                    if (i > e.maxx) e.maxx = i;
                    if (i > e.maxy) e.maxy = j;
                }
            }
        }

        return e;
    }
    
private:
    Color board_[SIZEX][SIZEY];
    int cap_[N_COLORS];
};

class Move {
    friend class Board;
private:
    struct Atom {
        enum Action { ADD, REMOVE } action_;
        Color color_;
        int x_, y_;
        
        Atom(Action action, Color color, int x, int y)
            : action_(action), color_(color), x_(x), y_(y)
        { }
    };

    std::list<Atom> atoms_;
};

Move* Board::create_move(Color color, int x, int y) const
{
    if (!in_range(x,y) || board_[x][y]) return 0;  // can't move on top of another piece
    Move* ret = new Move;
    ret->atoms_.push_back(Move::Atom(Move::Atom::ADD, color, x, y));

    static const int num_directions = 8;
    static const int directions[num_directions][2] = {
        { -1, -1 },
        { -1, 0 },
        { -1, 1 },
        { 0, -1 },
        { 0, 1 },
        { 1, -1 },
        { 1, 0 },
        { 1, 1 }
    };

    for (int d = 0; d < num_directions; d++) {
        int count = 0;
        int px = x + directions[d][0], py = y + directions[d][1];
        while (in_range(px,py) && board_[px][py] == other_color(color)) {
            count++;
            px += directions[d][0];
            py += directions[d][1];
        }
        if (in_range(px,py) && board_[px][py] == color && count % 2 == 1) {
            // capture!
            int cx = x + directions[d][0], cy = y + directions[d][1];
            while (in_range(cx,cy) && board_[cx][cy] == other_color(color)) {
                ret->atoms_.push_back(Move::Atom(Move::Atom::REMOVE, other_color(color), cx, cy));
                cx += directions[d][0];
                cy += directions[d][1];
            }
        }
    }

    return ret;
}

void Board::do_move(const Move* move) {
    for (std::list<Move::Atom>::const_iterator i = move->atoms_.begin();
            i != move->atoms_.end(); ++i) {
        if (i->action_ == Move::Atom::ADD) {
            board_[i->x_][i->y_] = i->color_;
        }
        else {
            board_[i->x_][i->y_] = NONE;
            cap_[other_color(i->color_)]++;
        }
    }
}

void Board::undo_move(const Move* move) {
    for (std::list<Move::Atom>::const_reverse_iterator i = move->atoms_.rbegin();
            i != move->atoms_.rend(); ++i) {
        if (i->action_ == Move::Atom::ADD) {
            board_[i->x_][i->y_] = NONE;
        }
        else {
            board_[i->x_][i->y_] = i->color_;
            cap_[other_color(i->color_)]--;
        }
    }
}


class Player {
public:
    virtual ~Player() { }

    virtual Move* move(const Board* board);
};

class AIPlayer {
public:
    AIPlayer(Color color) : color_(color) { }

    Move* move(const Board* board) {
        Board* b = const_cast<Board*>(board);  // I promise, it won't actually change

        int max_score = INT_MIN;
        std::auto_ptr<Move> max_move;
        
        BoardExtents ext = board->extents();
        ext.expand(AISEARCH);

        int randct = 0;
        for (int i = ext.minx; i <= ext.maxx; i++) {
            std::cout << i << " " << std::flush;
            for (int j = ext.miny; j <= ext.maxy; j++) {
                std::auto_ptr<Move> m(board->create_move(color_, i,j));
                if (!m.get()) continue;
                
                int pscore = score_move(b, color_, m.get(), AIDEPTH, ext);
                if (pscore > max_score) {
                    max_score = pscore;
                    max_move = m;
                    randct = 0;
                }
                else if (pscore == max_score) {
                    if (rand() % ++randct == 0) {
                        max_score = pscore;
                        max_move = m;
                    }
                }
            }
        }

        return max_move.release();
    }
private:
    int score_move(Board* board, Color color, Move* move, int depth, const BoardExtents& ext) {
        if (depth == 0) {
            return board->captures(color) - board->captures(other_color(color));
        }

        board->do_move(move);
        int max_score = INT_MIN;
        for (int i = ext.minx; i <= ext.maxx; i++) {
            for (int j = ext.miny; j <= ext.maxy; j++) {
                Move* m = board->create_move(color, i,j);
                if (!m) continue;

                int pscore = score_move(board, other_color(color), m, depth-1, ext);
                if (pscore > max_score) {
                    max_score = pscore;
                }
                delete m;
            }
        }
        board->undo_move(move);

        return -max_score;
    }
    
    Color color_;
};

void init()
{
    srand(time(NULL));
    INIT.init();
    
    glClearColor(0.5, 0.2, 0.05, 0);
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(-0.5, 18.5, -0.5, 18.5);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
}

void draw_grid()
{
    glColor3f(0, 0, 0);
    glBegin(GL_LINES);
    for (int i = 0; i < SIZEX; i++) {
        glVertex2f(i, 0);
        glVertex2f(i, SIZEY-1);
    }
    for (int j = 0; j < SIZEY; j++) {
        glVertex2f(0, j);
        glVertex2f(SIZEX-1, j);
    }
    glEnd();
}

void draw_board(const Board* b)
{
    draw_grid();
    glBegin(GL_QUADS);
    for (int i = 0; i < SIZEX; i++) {
        for (int j = 0; j < SIZEY; j++) {
            Color c = b->get_color(i,j);
            if (c == BLACK) {
                glColor3f(0,0,0);
            }
            else if (c == WHITE) {
                glColor3f(1,1,1);
            }
            
            if (c == BLACK || c == WHITE) {
                glVertex2f(i-0.4, j-0.4);
                glVertex2f(i+0.4, j-0.4);
                glVertex2f(i+0.4, j+0.4);
                glVertex2f(i-0.4, j+0.4);
            }
        }
    }
    glEnd();
}

void draw(const Board* b) {
    glClear(GL_COLOR_BUFFER_BIT);
    draw_board(b);
    SDL_GL_SwapBuffers();
}

void events() {
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        if (e.type == SDL_QUIT || e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
            SDL_Quit();
            exit(0);
        }
    }
}

int main()
{
    init();
    AIPlayer white(WHITE), black(BLACK);

    Board board;
    
    {
        Move* m = board.create_move(WHITE, 9, 9);
        board.do_move(m);
        delete m;
    }
    
    while (true) {
        draw(&board);
        events();

        {
            std::cout << "Black move\n";
            Move* m = black.move(&board);
            board.do_move(m);
            delete m;
        }
        
        draw(&board);
        events();

        {
            std::cout << "White move\n";
            Move* m = white.move(&board);
            board.do_move(m);
            delete m;
        }
    }
}
