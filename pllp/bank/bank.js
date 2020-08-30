/* state */

var SIZE = 7;
var PAUSE = 100;
var play = false; // animate solution
// state[id] === true when loggle with id is switched on
var state = new Array(SIZE);
var marks = new Array(SIZE);
var movesCount = 0;

function isSolved() {
    return state.indexOf(true) === -1;
}

function toggleState(id) {
    movesCount++;
    state[id] = !state[id];
}

function changeable(id) {
    if(id === SIZE - 1) {
        return true;
    }
    if(!state[id + 1]) {
        return false;
    }
    for(let i = id + 2; i < SIZE; i++) {
        if(state[i]) {
            return false;
        }
    }
    return true;
}

/* UI model */

function toggleToggle(id) {
    if(changeable(id)) {
        toggleState(id);
        unmarkToggle(id);
        updateAll();
    }
}

var updates = new Array(SIZE);
function updateAll() {
    updates.filter(f => typeof f === 'function')
        .forEach(f => f());
    const solved = document.getElementById('solved');
    solved.textContent = (
        isSolved()
            ? `You are done! At ${movesCount} move.`
            : ''
    );
}

function getLock() {
    return document.getElementById('lock');
}

function removeAllChildren(box) {
    while (box.firstChild) {
        //The list is LIVE so it will re-index each call
        box.removeChild(box.firstChild);
    }
}

function addToggle(id) {
    const toggle = document.createElement('span');

    const update = () => {
        toggle.style['background-color'] = state[id] ? 'green' : 'red';
        toggle.style['border-style'] = changeable(id) ? 'solid' : 'none';
        removeAllChildren(toggle);
        if(marks[id]) {
            let mark = document.createElement('div');
            mark.style['background-color'] = 'yellow';
            mark.style.width = '20px';
            mark.style.height = '20px';
            mark.style.margin = '15px'; // (50 - 20) / 2 = 15
            toggle.appendChild(mark);
        }
    };
    
    toggle.style.display = 'inline-block';
    toggle.style.width = '50px';
    toggle.style.height = '50px';
    toggle.style.margin = '5px';

    // border
    toggle.style['border-color'] = 'blue';
    toggle.style['border-width'] = '4px';

    update();
    toggle.onclick = event => toggleToggle(id);
    updates[id] = update;
    getLock().appendChild(toggle);
}


// helper to animate solution
function getToggle(id) {
    return getLock().childNodes[id];
}

function markToggle(id) {
    marks[id] = true;
    updateAll();
}

function unmarkToggle(id) {
    marks[id] = false;
    updateAll();
}

/* Solution */

// return index of next toggle to change - leftmost "on" toggle
function nextTarget() {
    return state.indexOf(true);
}

function nextMoveToChange(id) {
    if(changeable(id)) {
        return id;
    }
    return nextMoveToMakeChangeable(id);
}

function nextMoveToMakeChangeable(id) {
    if(id >= SIZE) {
        throw new Error(`Out of range. id = ${id} >= SIZE = ${SIZE}`);
    }
    if(changeable(id)) {
        throw new Error(`Nothing to do to make toggle #${id} changeable`);
    }
    // nearest neighbour on the right of the lock with id
    const nb = id + 1;
    if(!state[nb]) {
        // if nb is "off", make it "on"
        return nextMoveToChange(nb);
    } else {
        // nb is "on" so we have to make all next toggles "off"
        for(let next = nb + 1; next < SIZE; next++) {
            if(state[next]) {
                return nextMoveToChange(next);
            } else {
                continue;
            }
        }
        throw new Error(`Can not make toggle #${id} changeable`);
    }
}

function nextMove() {
    if(isSolved()) {
        return -1;
    }
    const target = nextTarget();
    if (target === -1) {
        throw new Error('you must be done');
    }
    return nextMoveToChange(target);
}

/* UI to explore solution */
function markNextMove() {
    const move = nextMove();
    if(move >= 0) {
        markToggle(move);
    }
    return move;
}

/* Animate solution */
function stop() {
    play = false;
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

async function startPlay() {
    play = true;
    while(play) {
        const move = markNextMove();
        await sleep(PAUSE);
        toggleToggle(move);
        await sleep(PAUSE);
    }
}

function initState() {
    state.fill(true);
    marks.fill(false);
    movesCount = 0;
    stop();
}

function init() {
    // clear on reload file (e.g. using skewer)
    removeAllChildren(getLock());

    // init toggles
    for(let i = 0; i < SIZE; i++) {
        addToggle(i);
    }
    updateAll();

    // set event handlers
    document.getElementById('markNextMove').onclick = markNextMove;
    document.getElementById('pause').onclick = stop;
    document.getElementById('play').onclick = startPlay;
    document.getElementById('reset').onclick = () => {
        initState();
        updateAll();
    };
}

initState();
init();
