#include "str_solver.hpp"

int main(int argc, char* argv[]) {
    cout << "Start solving..." << endl;
    StrSolver solver((string(argv[1])));
    solver.solve1(string(argv[2]));
    return 0;
}
