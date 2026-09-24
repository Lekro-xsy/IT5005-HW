import json
import time
import streamlit as st
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
)

st.title('Sudoku Solver')

with open('puzzles.json') as f:
    pool = json.load(f)

def get_givens(item):
    answer = {}
    for key, value in item['givens'].items():
        r, c = key.split('_')
        answer[(int(r), int(c))] = value
    return answer


def show_board(n, box_h, box_w, givens, solved=None):
    html = '<table style="border-collapse:collapse;margin:10px 0">'
    for r in range(1, n + 1):
        html += '<tr>'
        for c in range(1, n + 1):
            value = givens.get((r, c), '')
            colour = '#dbeafe' if (r, c) in givens else 'white'
            weight = 'bold' if (r, c) in givens else 'normal'
            if solved is not None and (r, c) in solved:
                value = solved[(r, c)]
                if (r, c) not in givens:
                    colour = '#dcfce7'

            top = 3 if r == 1 or (r - 1) % box_h == 0 else 1
            left = 3 if c == 1 or (c - 1) % box_w == 0 else 1
            bottom = 3 if r == n else 1
            right = 3 if c == n else 1
            style = (
                'width:42px;height:42px;text-align:center;'
                f'background:{colour};font-weight:{weight};'
                f'border-top:{top}px solid black;'
                f'border-left:{left}px solid black;'
                f'border-bottom:{bottom}px solid black;'
                f'border-right:{right}px solid black'
            )
            html += f'<td style="{style}">{value}</td>'
        html += '</tr>'
    html += '</table>'
    st.markdown(html, unsafe_allow_html=True)


def split_atom(item):
    name = str(item)
    match name:
        case text if text.startswith('Is'):
            kind = 'Is'
        case text if text.startswith('Not'):
            kind = 'Not'
        case _:
            return '', 0, 0, 0
    r, c, v = name[len(kind):].split('_')
    return kind, int(r), int(c), int(v)


def explain_step(conclusion, premises, box_h, box_w):
    kind, r, c, v = split_atom(conclusion)
    if not premises:
        return f'Cell ({r}, {c}) is given as {v}.'

    first_kind, first_r, first_c, first_v = split_atom(premises[0])
    if kind == 'Not' and len(premises) == 1 and first_kind == 'Is':
        if (r, c) == (first_r, first_c):
            reason = f'the cell already has value {first_v}'
        elif r == first_r:
            reason = f'row {r} already has {v}'
        elif c == first_c:
            reason = f'column {c} already has {v}'
        elif ((r - 1) // box_h == (first_r - 1) // box_h and
              (c - 1) // box_w == (first_c - 1) // box_w):
            reason = f'the same box already has {v}'
        else:
            reason = 'a related cell already has this value'
        return f'Remove {v} from cell ({r}, {c}) because {reason}.'

    if kind == 'Is':
        return f'Cell ({r}, {c}) must be {v} because all other values were removed.'
    return 'This conclusion follows from the earlier steps.'


def make_trace(kb, query):
    trace = []
    added = set()

    def add(goal):
        if goal in added:
            return
        if goal in kb._bc_facts:
            trace.append((goal, []))
        elif goal in kb._bc_proof:
            premises, rule = kb._bc_proof[goal]
            for premise in premises:
                add(premise)
            trace.append((goal, list(premises)))
        added.add(goal)

    add(query)
    return trace


n = pool['n']
box_h = pool['box_h']
box_w = pool['box_w']

number = st.selectbox(
    'Choose a puzzle',
    range(len(pool['puzzles'])),
    format_func=lambda x: 'Puzzle ' + str(x + 1),
)
givens = get_givens(pool['puzzles'][number])

if st.session_state.get('puzzle_number') != number:
    st.session_state['puzzle_number'] = number
    st.session_state.pop('solved_grid', None)
    st.session_state.pop('query_answer', None)

st.subheader('Puzzle')
show_board(n, box_h, box_w, givens, st.session_state.get('solved_grid'))
st.caption('Blue cells are givens. Green cells are values found by the solver.')

algorithm = st.radio('Choose an algorithm', ['Forward chaining', 'Backward chaining'])
if st.button('Solve full grid'):
    match algorithm:
        case 'Forward chaining':
            solver = solve_full_grid_fc
        case 'Backward chaining':
            solver = solve_full_grid_bc

    start = time.time()
    result = solver(n, box_h, box_w, givens)
    elapsed = time.time() - start
    st.session_state['solved_grid'] = result
    st.success('Solved in ' + f'{elapsed:.2f}' + ' seconds')
    show_board(n, box_h, box_w, givens, result)

st.subheader('Cell query')
col1, col2, col3 = st.columns(3)
with col1:
    query_r = st.number_input('Row', 1, n, 1)
with col2:
    query_c = st.number_input('Column', 1, n, 1)
with col3:
    query_v = st.number_input('Value', 1, n, 1)

if st.button('Check entailment'):
    query_kb = build_definite_kb(n, box_h, box_w, givens)
    query = atom('Is', int(query_r), int(query_c), int(query_v))
    answer = pl_bc_entails(query_kb, query)
    trace = make_trace(query_kb, query) if answer else []
    st.session_state['query_answer'] = (answer, trace, query)

if 'query_answer' in st.session_state:
    answer, trace, query = st.session_state['query_answer']
    st.write('Entailed:', answer)
    st.markdown('#### Tutor mode')
    if not answer:
        st.info('The givens and rules do not prove this value for the selected cell.')
    else:
        if len(trace) > 100:
            st.info('The proof is long, so the final 100 steps are shown.')
            trace = trace[-100:]
        for i, (conclusion, premises) in enumerate(trace, 1):
            sentence = explain_step(conclusion, premises, box_h, box_w)
            with st.expander('Step ' + str(i)):
                st.write(sentence)
