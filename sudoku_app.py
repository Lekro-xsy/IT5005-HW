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


def render_board(n, box_h, box_w, givens, solved=None, focus=None):
    cells = []
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            value = givens.get((r, c), '')
            css_class = 'given' if (r, c) in givens else 'empty'
            label = 'given' if (r, c) in givens else 'empty'

            if solved is not None and (r, c) in solved:
                value = solved[(r, c)]
                if (r, c) not in givens:
                    css_class = 'inferred'
                    label = 'inferred'

            if focus == (r, c):
                css_class += ' focused'

            borders = []
            if r == 1 or (r - 1) % box_h == 0:
                borders.append('border-top-width:3px')
            if c == 1 or (c - 1) % box_w == 0:
                borders.append('border-left-width:3px')
            if r == n:
                borders.append('border-bottom-width:3px')
            if c == n:
                borders.append('border-right-width:3px')

            cells.append(
                f'<div class="sudoku-cell {css_class}" '
                f'style="{";".join(borders)}" '
                f'aria-label="row {r}, column {c}, {label} {value}">'
                f'{value}</div>'
            )

    st.markdown(
        f'<div class="sudoku-grid" '
        f'style="grid-template-columns:repeat({n}, minmax(34px, 52px))">'
        f'{"".join(cells)}</div>',
        unsafe_allow_html=True,
    )


def parse_atom_name(name):
    match name:
        case str() if name.startswith('Is'):
            prefix = 'Is'
        case str() if name.startswith('Not'):
            prefix = 'Not'
        case _:
            raise ValueError(f'Unrecognised atom: {name}')

    r, c, value = (int(part) for part in name[len(prefix):].split('_'))
    return prefix, r, c, value


def explain_trace_step(step, box_h, box_w):
    kind = step['kind']
    conclusion = step['conclusion']
    prefix, r, c, value = parse_atom_name(conclusion)

    match kind:
        case 'fact':
            return f'Given: cell ({r}, {c}) contains {value}.'
        case 'failure':
            return (
                f'No rule chain from the givens proves that cell ({r}, {c}) '
                f'contains {value}.'
            )
        case 'rule':
            pass
        case _:
            raise ValueError(f'Unrecognised trace event: {kind}')

    premises = [parse_atom_name(name) for name in step['premises']]
    if prefix == 'Not' and len(premises) == 1 and premises[0][0] == 'Is':
        _, source_r, source_c, source_value = premises[0]
        if (source_r, source_c) == (r, c):
            return (
                f'Eliminate {value} from cell ({r}, {c}): the cell is '
                f'already fixed to {source_value}.'
            )
        if source_r == r:
            reason = f'row {r} already contains {value} at column {source_c}'
        elif source_c == c:
            reason = f'column {c} already contains {value} at row {source_r}'
        elif (
            (source_r - 1) // box_h == (r - 1) // box_h
            and (source_c - 1) // box_w == (c - 1) // box_w
        ):
            reason = (
                f'the same {box_h}x{box_w} box already contains {value} '
                f'at ({source_r}, {source_c})'
            )
        else:
            reason = f'a peer cell ({source_r}, {source_c}) contains {value}'
        return f'Eliminate {value} from cell ({r}, {c}): {reason}.'

    if prefix == 'Is' and premises and all(item[0] == 'Not' for item in premises):
        removed = ', '.join(str(item[3]) for item in premises)
        return (
            f'Deduce {value} at cell ({r}, {c}): all other candidates '
            f'({removed}) have been eliminated.'
        )

    readable = ', '.join(step['premises'])
    return f'From {readable}, infer {conclusion}.'


def build_trace(kb, query, entailed):
    if not entailed:
        return [{'kind': 'failure', 'conclusion': str(query), 'premises': []}]

    trace = []
    emitted = set()

    def add_step(goal):
        if goal in emitted:
            return
        if goal in kb._bc_facts:
            trace.append({'kind': 'fact', 'conclusion': str(goal), 'premises': []})
        else:
            premises, unused_rule = kb._bc_proof[goal]
            for premise in premises:
                add_step(premise)
            trace.append(
                {
                    'kind': 'rule',
                    'conclusion': str(goal),
                    'premises': [str(premise) for premise in premises],
                }
            )
        emitted.add(goal)

    add_step(query)
    return trace


st.markdown(
    """
    <style>
    .stApp { background: #f7f8fb; }
    .sudoku-grid {
        display: grid;
        width: fit-content;
        margin: .5rem auto 1rem;
        background: #0f172a;
        box-shadow: 0 10px 26px rgba(15, 23, 42, .13);
    }
    .sudoku-cell {
        box-sizing: border-box;
        width: 52px;
        height: 52px;
        display: flex;
        align-items: center;
        justify-content: center;
        border: 1px solid #94a3b8;
        background: white;
        color: #0f172a;
        font-size: 1.25rem;
        font-weight: 650;
    }
    .sudoku-cell.given { background: #dbeafe; color: #1e3a8a; }
    .sudoku-cell.inferred { background: #ecfdf5; color: #047857; }
    .sudoku-cell.empty { color: #94a3b8; }
    .sudoku-cell.focused { box-shadow: inset 0 0 0 4px #f59e0b; }
    .legend { text-align: center; color: #475569; font-size: .9rem; }
    @media (max-width: 720px) {
        .sudoku-cell { width: 38px; height: 38px; font-size: 1rem; }
    }
    </style>
    """,
    unsafe_allow_html=True,
)

n = pool['n']
box_h = pool['box_h']
box_w = pool['box_w']
puzzle_pool = []
for item in pool['puzzles']:
    givens = {
        tuple(int(part) for part in key.split('_')): value
        for key, value in item['givens'].items()
    }
    puzzle_pool.append({'givens': givens, 'given_count': item['given_count']})

with st.sidebar:
    st.header('Puzzle controls')
    selected_index = st.selectbox(
        'Choose a puzzle',
        range(len(puzzle_pool)),
        format_func=lambda index: (
            f'Puzzle {index + 1} · '
            f'{puzzle_pool[index]["given_count"]} givens'
        ),
    )
    algorithm = st.radio(
        'Inference algorithm',
        ('Forward chaining', 'Backward chaining'),
        help='Both use the same definite-clause knowledge base.',
    )
    st.caption('Blue cells are givens. Green cells are inferred by the solver.')

if st.session_state.get('selected_index') != selected_index:
    st.session_state.selected_index = selected_index
    st.session_state.pop('solve_result', None)
    st.session_state.pop('query_result', None)

puzzle = puzzle_pool[selected_index]
givens = puzzle['givens']

board_column, solve_column = st.columns([1.25, 1], gap='large')
with board_column:
    st.subheader(f'Puzzle {selected_index + 1}')
    current_solution = st.session_state.get('solve_result')
    solved_grid = None
    if current_solution and current_solution['puzzle'] == selected_index:
        solved_grid = current_solution['grid']
    render_board(n, box_h, box_w, givens, solved_grid)
    st.markdown(
        '<div class="legend">■ Given &nbsp;&nbsp; '
        '<span style="color:#047857">■ Inferred</span></div>',
        unsafe_allow_html=True,
    )

with solve_column:
    st.subheader('Full-grid solver')
    st.write(
        'Build the Horn knowledge base once, then reconstruct every cell '
        'using the selected inference procedure.'
    )
    if st.button('Solve full grid', type='primary', use_container_width=True):
        match algorithm:
            case 'Forward chaining':
                solver = solve_full_grid_fc
            case 'Backward chaining':
                solver = solve_full_grid_bc
        with st.spinner(f'Running {algorithm.lower()}...'):
            started = time.perf_counter()
            try:
                grid = solver(n, box_h, box_w, givens)
                elapsed = time.perf_counter() - started
                st.session_state.solve_result = {
                    'puzzle': selected_index,
                    'grid': grid,
                    'elapsed': elapsed,
                    'algorithm': algorithm,
                }
                st.rerun()
            except ValueError as error:
                st.error(str(error))

    result = st.session_state.get('solve_result')
    if result and result['puzzle'] == selected_index:
        metric_a, metric_b = st.columns(2)
        metric_a.metric('Algorithm', result['algorithm'])
        metric_b.metric('Elapsed time', f'{result["elapsed"]:.3f} s')
        st.success('Every cell was entailed by the knowledge base.')

st.divider()
st.subheader('Targeted entailment query')
st.write(
    'Ask whether a particular proposition '
    r'$\mathit{Is}_{r,c,v}$ is entailed. Tutor mode shows the proof in '
    'plain English.'
)

input_r, input_c, input_v, query_button = st.columns([1, 1, 1, 1.35])
with input_r:
    row = st.number_input('Row', 1, n, 1, 1)
with input_c:
    column = st.number_input('Column', 1, n, 1, 1)
with input_v:
    value = st.number_input('Value', 1, n, 1, 1)
with query_button:
    st.write('')
    st.write('')
    run_query = st.button('Run query', use_container_width=True)

if run_query:
    started = time.perf_counter()
    kb = build_definite_kb(n, box_h, box_w, givens)
    query = atom('Is', int(row), int(column), int(value))
    verdict = pl_bc_entails(kb, query)
    trace = build_trace(kb, query, verdict)
    elapsed = time.perf_counter() - started
    st.session_state.query_result = {
        'puzzle': selected_index,
        'row': int(row),
        'column': int(column),
        'value': int(value),
        'verdict': verdict,
        'elapsed': elapsed,
        'trace': trace,
    }

query_result = st.session_state.get('query_result')
if query_result and query_result['puzzle'] == selected_index:
    query_text = (
        f'Is cell ({query_result["row"]}, {query_result["column"]}) '
        f'equal to {query_result["value"]}?'
    )
    if query_result['verdict']:
        st.success(f'{query_text}  True')
    else:
        st.error(f'{query_text}  False')
    st.caption(f'Query completed in {query_result["elapsed"]:.3f} seconds.')

    st.markdown('#### Tutor mode · reasoning trace')
    trace = query_result['trace']
    if len(trace) > 160:
        st.info(
            f'The proof contains {len(trace)} events. Showing the final 160 '
            'steps that lead most directly to the query.'
        )
        trace = trace[-160:]

    for step_number, step in enumerate(trace, 1):
        explanation = explain_trace_step(step, box_h, box_w)
        with st.expander(f'Step {step_number}: {explanation}'):
            if step['premises']:
                st.caption('Premises: ' + ', '.join(step['premises']))
            st.caption('Conclusion: ' + step['conclusion'])
