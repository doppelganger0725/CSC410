import argparse

parser = argparse.ArgumentParser(description="game parser")

class PointState:
    def __init__(self, x, y, player, _parent=None):
        self.x = x
        self.y = y
        self.state = self._check_state(x, y)
        self.player = player
        self.parent = _parent
        self.results_chain = set()
        self.preserved = None

    def _check_state(self, x, y):
        if x == 0 and y == 0:
            return "A"
        if x == y:
            return "B"
        if x == 0 or y == 0:
            return "C"
        if (x == 1 and y == 2) or (y == 1 and x == 2):
            return "D"

        return "E"

    def get_state(self):
        return self.state
    
    def who_win(self):
        if self.state == "A":
            return self.player
        if self.state == "B":
            return self._other_player()
        if self.state == "C":
            return self._other_player()
        if self.state == "D":
            return self._other_player()
        return -1

    def _other_player(self):
        return self.player ^ 3

    def next_state(self, preserved = False, no_parents = False):
        parent = None if no_parents else self
        if self.preserved != None:
            return self.preserved
        ret = []
        for nx in range(0, self.x):
            ret.append(PointState(nx, self.y, self._other_player(), parent))
        for ny in range(0, self.y):
            ret.append(PointState(self.x, ny, self._other_player(), parent))
        for i in range(1, min(self.x, self.y)):
            ret.append(PointState(self.x - i, self.y - i, self._other_player(), parent))

        ret = set(ret)

        if preserved:
            self.preserved = ret
        return ret

    def append_result(self, result):
        self.results_chain.add(result)
        if self.parent != None:
            self.parent.append_result(result)

    def all_equals(self, v=None):
        if len(self.results_chain) != 1:
            return False
        if self.who_win() != -1:
            return self.parent.all_equals(self.who_win()) if self.parent != None else True
        if v != None:
            r1 = all([x == v for x in self.results_chain])
            return r1 and self.parent.all_equals(v) if self.parent != None else r1
        return False
        
    def __hash__(self):
        return hash(self.state) + hash(self.player) * 32 + hash(self.x) * 64 + hash(self.y) * 128
    
    def __eq__(self, other) -> bool:
        return isinstance(other, PointState) and self.state == other.state and self.player == other.player \
            and self.x == other.x and self.y == other.y
            
    def __lt__(self, other):
        if self.state != other.state:
            return self.state < other.state
        return self.x < other.x or self.y < other.y

    def __str__(self):
        return "{{x: {}, y: {}, state: {}, player: {}, result: {}}}".format(self.x, self.y, self.state, self.player, self.results_chain)

def solution(x, y):
    # E U B \vee A \vee C
    curState = PointState(x, y, 2) # player 1 should make the initial move, so initialize 2 as the first one
    state_sets = curState.next_state(True, True)
    if len(state_sets) == 0:
        return 1
    prev = set()
    # until in ctl
    while state_sets != prev:
        prev = state_sets
        cur_set = state_sets
        for state in sorted(list(cur_set)):
            state_sets = state_sets.union(state.next_state())
    
    for state in sorted(list(state_sets)):
        if state.who_win() != -1:
            state.append_result(state.who_win())
    # print([str(x) for x in curState.next_state()])
    results = set()
    for state in state_sets:
        if state.who_win() != -1 and state.all_equals():
            results.add(state.who_win())

    for r in sorted(list(results)):
        return r
    return 1

if __name__ == "__main__":
    parser.add_argument("x", type=int)
    parser.add_argument("y", type=int)
    args = parser.parse_known_args()
    known_args, unknown_args = args
    x = known_args.x
    y = known_args.y
    print(solution(x, y))

