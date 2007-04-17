#include <soy/init.h>
#include <soy/ptr.h>
#include <soy/Viewport.h>
#include <list>
#include <GL/gl.h>
#include <GL/glu.h>
#include <memory>
#include <iostream>
#include <queue>

const int SIZEX = 19, SIZEY = 19;
const int WHITEDEPTH = 5;
const int BLACKDEPTH = 5;

SoyInit INIT;
Viewport VIEW(vec2(SIZEX/2.0-0.5, SIZEY/2.0-0.5), vec2(SIZEX+0.5, SIZEY));

enum Color { NONE, WHITE, BLACK, N_COLORS };
inline Color other_color(Color in) {
    return in == WHITE ? BLACK : WHITE;
}

class Move;

class Board {
public:
    Board() {
        for (int i = 0; i < SIZEX; i++) {
            for (int j = 0; j < SIZEY; j++) {
                board_[i][j] = NONE;
            }
        }

        board_[8 ][5] = WHITE;
        board_[8 ][6] = WHITE;
        board_[8 ][7] = WHITE;
        board_[9 ][7] = WHITE;
        board_[10][7] = WHITE;
        board_[10][6] = WHITE;
        board_[10][5] = WHITE;

        board_[8 ][13] = BLACK;
        board_[8 ][12] = BLACK;
        board_[8 ][11] = BLACK;
        board_[9 ][11] = BLACK;
        board_[10][11] = BLACK;
        board_[10][12] = BLACK;
        board_[10][13] = BLACK;

        justcapx_ = justcapy_ = -1;

        compute_extrema();
        advance_[NONE] = 0;
        
        for (int i = 0; i < N_COLORS; i++) {
            cap_[i] = 0;
        }
    }

    Move* create_move(Color color, int x, int y) const;
    void do_move(Move* move);
    void undo_move(const Move* move);
    bool in_range(int x, int y) const {
        return 0 <= x && x < SIZEX && 0 <= y && y < SIZEY;
    }
    int captures(Color color) const {
        return cap_[color];
    }
    bool win(Color color) const {
        return captures(color) >= 5;
    }
    Color get_color(int x, int y) const {
        return board_[x][y];
    }
    int neighbors(Color c, int x, int y) const {
        int ret = 0;
        for (int i = x-1; i <= x+1; i++) {
            for (int j = y-1; j <= y+1; j++) {
                if (i == x && j == y) continue;
                if (!in_range(i,j)) continue;
                if (get_color(i,j) == c) ret++;
            }
        }
        return ret;
    }

    int advance_score(Color c) const {
        if (c == WHITE) {
            return 12 - advance_[c];
        }
        else {
            return advance_[c] - 6;
        }
    }
    
    void compute_extrema() {
        for (int y = SIZEY-1; y >= 0; y--) {
            for (int x = 0; x < SIZEX; x++) {
                if (get_color(x,y) == WHITE) {
                    advance_[WHITE] = y;
                    goto L_ENDWHITE;
                }
            }
        }
L_ENDWHITE:
        for (int y = 0; y < SIZEY; y++) {
            for (int x = 0; x < SIZEX; x++) {
                if (get_color(x,y) == BLACK) {
                    advance_[BLACK] = y;
                    goto L_ENDBLACK;
                }
            }
        }
L_ENDBLACK:
        return;
    }
    
private:
    
    Color board_[SIZEX][SIZEY];
    int cap_[N_COLORS];
    int advance_[N_COLORS];
    int justcapx_, justcapy_;
};

class Move {
    friend class Board;
    Move(bool capture, int x, int y, Color oldstate, Color newstate, int oldjustcapx, int oldjustcapy)
        : capture(capture), x(x), y(y), newstate(newstate), oldstate(oldstate), oldjustcapx(oldjustcapx), oldjustcapy(oldjustcapy)
    {
        for (int i = 0; i < N_COLORS; i++) {
            deltacap[i] = dadvance[i] = 0;
        }
        oldjustcapx = oldjustcapy = -1;
    }
    
private:
    bool capture;
    int x, y;
    Color newstate;
    Color oldstate;
    int oldjustcapx, oldjustcapy;
    int deltacap[N_COLORS];
    int dadvance[N_COLORS];
};

Move* Board::create_move(Color color, int x, int y) const
{
    if (!in_range(x,y)) return 0;
    int neigh = neighbors(color,x,y);
    if (get_color(x,y) == color) { // remove
        if (neigh <= 1 || neigh >= 4) {
            return new Move(false,x, y, color, NONE, justcapx_, justcapy_);
        }
        else {
            return 0;
        }
    }
    else {
        if (neigh == 3) {
            if (get_color(x,y) == NONE) { // add
                return new Move(false, x, y, NONE, color, justcapx_, justcapy_);
            }
            else {    // capture
                if (x == justcapx_ && y == justcapy_) return 0; // ko rule
                Move* move = new Move(true, x, y, get_color(x,y), color, justcapx_, justcapy_);
                move->deltacap[color]++;
                return move;
            }
        }
        else {
            return 0;
        }
    }
}

void Board::do_move(Move* move) {
    board_[move->x][move->y] = move->newstate;
    if (move->capture) {
        justcapx_ = move->x;
        justcapy_ = move->y;
    }
    else {
        justcapx_ = justcapy_ = -1;
    }
    for (int i = 0; i < N_COLORS; i++) {
        cap_[i] += move->deltacap[i];
    }
    int oldad = advance_[move->oldstate];
    int newad = advance_[move->newstate];
    assert(move->oldstate != move->newstate);
    if (move->y == oldad
        || move->newstate == WHITE && move->y > advance_[WHITE]
        || move->newstate == BLACK && move->y < advance_[BLACK]) {

        compute_extrema();
        move->dadvance[move->newstate] = advance_[move->newstate] - newad;
        move->dadvance[move->oldstate] = advance_[move->oldstate] - oldad;
    }
}

void Board::undo_move(const Move* move) {
    board_[move->x][move->y] = move->oldstate;
    justcapx_ = move->oldjustcapx;
    justcapy_ = move->oldjustcapy;
    for (int i = 0; i < N_COLORS; i++) {
        cap_[i] -= move->deltacap[i];
        advance_[i] -= move->dadvance[i];
    }
}


class Player {
public:
    virtual ~Player() { }

    virtual Move* move(const Board* board);
};

class AIPlayer {
public:
    AIPlayer(Color color, int depth) : color_(color), depth_(depth) { }

    Move* move(const Board* board) {
        Board* b = const_cast<Board*>(board);  // I promise, it won't actually change

        float max_score = -HUGE_VAL;
        std::auto_ptr<Move> max_move;

        int randct = 0;
        for (int i = 0; i < SIZEX; i++) {
            std::cout << i << " " << std::flush;
            for (int j = 0; j < SIZEY; j++) {
                std::auto_ptr<Move> m(board->create_move(color_, i,j));
                if (!m.get()) continue;
                
                float pscore = score_move(b, color_, m.get(), depth_);
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
    
    static float advance_to_score(int ascore) {
        if (ascore <= 0) return HUGE_VAL;
        else return 2.0 / ascore;
    }

    static float captures_to_score(int cap) {
        if (cap >= 5) return HUGE_VAL;
        else return cap;
    }
    
    float score_board(const Board* board, Color color) const {
        return board->captures(color) - board->captures(other_color(color))
            + advance_to_score(board->advance_score(color)) 
            - advance_to_score(board->advance_score(other_color(color)));
    }
private:

    float score_move(Board* board, Color color, Move* move, int depth) {
        board->do_move(move);

        if (depth == 0) {
            float ret = score_board(board, color);
            board->undo_move(move);
            return ret;
        }

        float max_score = -HUGE_VAL;
        for (int i = 0; i < SIZEX; i++) {
            for (int j = 0; j < SIZEY; j++) {
                Move* m = board->create_move(other_color(color), i,j);
                if (!m) continue;

                float pscore = score_move(board, other_color(color), m, depth-1);
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
    int depth_;
};

class HumanPlayer
{
public:
    HumanPlayer(Color c) : color_(c) { }
    
    Move* move(const Board* b) {
        SDL_Event e;
        while (SDL_WaitEvent(&e)) {
            if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE
                || e.type == SDL_QUIT) {
                INIT.quit();
                exit(0);
            }

            if (e.type == SDL_MOUSEBUTTONDOWN) {
                vec2 wp = coord_convert(INIT.pixel_view(), VIEW, vec2(e.button.x, e.button.y));
                int x = int(wp.x+0.5);
                int y = int(wp.y+0.5);

                Move* m = b->create_move(color_, x, y);
                if (m) return m;
            }
        }
    }
private:
    Color color_;
};

void init()
{
    srand(time(NULL));
    INIT.init();
    
    glClearColor(0.5, 0.2, 0.05, 0);
    VIEW.activate();
    glLoadIdentity();
}

void draw_grid()
{
    glColor3f(0, 0, 0);
    glLineWidth(1.0);
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

    glLineWidth(2.0);
    glColor3f(0.5,1,0.5);
    glBegin(GL_LINES);
        glVertex2f(0,6);
        glVertex2f(SIZEX-1,6);
        glVertex2f(0,12);
        glVertex2f(SIZEY-1,12);
    glEnd();

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

    glColor3f(0,0,0);
    glBegin(GL_QUADS);
    for (int i = 0; i < b->captures(WHITE); i++) {
        glVertex2f(SIZEX-1+0.1, i + 0.1);
        glVertex2f(SIZEX-1+0.9, i + 0.1);
        glVertex2f(SIZEX-1+0.9, i + 0.9);
        glVertex2f(SIZEX-1+0.1, i + 0.9);
    }
    glEnd();
    
    glColor3f(1,1,1);
    glBegin(GL_QUADS);
    for (int i = 0; i < b->captures(BLACK); i++) {
        glVertex2f(-0.1, SIZEY - 2 - i + 0.1);
        glVertex2f(-0.9, SIZEY - 2 - i + 0.1);
        glVertex2f(-0.9, SIZEY - 2 - i + 0.9);
        glVertex2f(-0.1, SIZEY - 2 - i + 0.9);
    }
    glEnd();
}

void draw_legal_moves(const Board* b)
{
    glLineWidth(2.0);
    for (int i = 0; i < SIZEX; i++) {
        for (int j = 0; j < SIZEY; j++) {
            float rad = 0.43;
            Move* m = b->create_move(WHITE, i,j);
            if (m) {
                delete m;
                glColor3f(0.7,0.7,0.7);
                glBegin(GL_LINE_LOOP);
                glVertex2f(i - rad, j - rad);
                glVertex2f(i - rad, j + rad);
                glVertex2f(i + rad, j + rad);
                glVertex2f(i + rad, j - rad);
                glEnd();
                rad += 0.06;
            }

            m = b->create_move(BLACK, i,j);
            if (m) {
                delete m;
                glColor3f(0.3,0.3,0.3);
                glBegin(GL_LINE_LOOP);
                glVertex2f(i - rad, j - rad);
                glVertex2f(i - rad, j + rad);
                glVertex2f(i + rad, j + rad);
                glVertex2f(i + rad, j - rad);
                glEnd();
            }
        }
    }
}

void draw(const Board* b) {
    glClear(GL_COLOR_BUFFER_BIT);
    draw_board(b);
    draw_legal_moves(b);
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

void waitevents() {
    SDL_Event e;
    while (SDL_WaitEvent(&e)) {
        if (e.type == SDL_QUIT || e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
            SDL_Quit();
            exit(0);
        }
        if (e.type == SDL_KEYDOWN) {
            break;
        }
    }
}

int main()
{
    init();
    HumanPlayer white(WHITE);
    AIPlayer black(BLACK, BLACKDEPTH);

    Board board;
    
    while (true) {
        draw(&board);

        {
            std::cout << "Black move\n";
            Move* m = black.move(&board);
            if (!m) break;
            board.do_move(m);
            delete m;
        }
        
        draw(&board);

        {
            std::cout << "White move\n";
            Move* m = white.move(&board);
            if (!m) break;
            board.do_move(m);
            delete m;
        }
    }

    while (true) waitevents();
}
