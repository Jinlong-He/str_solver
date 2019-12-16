#include "str_solver.hpp"

int main(int argc, char* argv[]) {
    cout << "I'm in..." << endl;
    StrSolver solver((string(argv[1])));
    solver.solve(string(argv[2]));
    return 0;
}
