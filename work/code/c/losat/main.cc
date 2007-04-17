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
const int WHITEDEPTH = 4;
const int BLACKDEPTH = 4;

SoyInit INIT;
Viewport VIEW(vec2(SIZEX/2.0-0.5, SIZEY/2.0-0.5), vec2(SIZEX, SIZEY));

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

        board_[8 ][6] = WHITE;
        board_[8 ][7] = WHITE;
        board_[8 ][8] = WHITE;
        board_[9 ][8] = WHITE;
        board_[10][8] = WHITE;
        board_[10][7] = WHITE;
        board_[10][6] = WHITE;

        board_[9 ][12] = BLACK;
        board_[9 ][11] = BLACK;
        board_[9 ][10] = BLACK;
        board_[10][10] = BLACK;
        board_[11][10] = BLACK;
        board_[11][11] = BLACK;
        board_[11][12] = BLACK;

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
            return advance_[c];
        }
        else {
            return SIZEY - advance_[c];
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
};

class Move {
    friend class Board;
    Move(int x, int y, Color oldstate, Color newstate)
        : x(x), y(y), newstate(newstate), oldstate(oldstate)
    {
        for (int i = 0; i < N_COLORS; i++) {
            deltacap[i] = dadvance[i] = 0;
        }
    }
    
private:
    int x, y;
    Color newstate;
    Color oldstate;
    int deltacap[N_COLORS];
    int dadvance[N_COLORS];
};

Move* Board::create_move(Color color, int x, int y) const
{
    if (!in_range(x,y)) return 0;
    int neigh = neighbors(color,x,y);
    if (get_color(x,y) == color) { // remove
        if (neigh <= 1 || neigh >= 4) {
            return new Move(x, y, color, NONE);
        }
        else {
            return 0;
        }
    }
    else {
        if (neigh == 3) {
            if (get_color(x,y) == NONE) { // add
                return new Move(x, y, NONE, color);
            }
            else {    // capture
                Move* move = new Move(x, y, get_color(x,y), color);
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

        int max_score = INT_MIN;
        std::auto_ptr<Move> max_move;

        int randct = 0;
        for (int i = 0; i < SIZEX; i++) {
            std::cout << i << " " << std::flush;
            for (int j = 0; j < SIZEY; j++) {
                for (int c = WHITE; c < N_COLORS; c++) {
                    std::auto_ptr<Move> m(board->create_move((Color)c, i,j));
                    if (!m.get()) continue;
                    
                    int pscore = score_move(b, color_, m.get(), depth_);
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
        }
        return max_move.release();
    }
    
    int score_board(const Board* board, Color color) const {
        return board->captures(color) - board->captures(other_color(color))
            + board->advance_score(color) - board->advance_score(other_color(color));
    }
private:

    int score_move(Board* board, Color color, Move* move, int depth) {
        board->do_move(move);

        if (depth == 0) {
            int ret = score_board(board, color);
            board->undo_move(move);
            return ret;
        }

        int max_score = INT_MIN;
        for (int i = 0; i < SIZEX; i++) {
            for (int j = 0; j < SIZEY; j++) {
                for (int c = WHITE; c < N_COLORS; c++) {
                    Move* m = board->create_move((Color)c, i,j);
                    if (!m) continue;

                    int pscore = score_move(board, other_color(color), m, depth-1);
                    if (pscore > max_score) {
                        max_score = pscore;
                    }
                    delete m;
                }
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
                Color c = e.button.button == SDL_BUTTON_LEFT ? WHITE : BLACK;

                Move* m = b->create_move(c, x, y);
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
