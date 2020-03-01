Object.entries(lock.children).forEach(([id, child]) => lock.removeChild(child));

var SIZE = 7;
var lock = document.getElementById('lock');

var state = new Array(SIZE).fill(false);
var updates = new Array(SIZE);
function updateAll() {
    updates.filter(f => typeof f === 'function')
        .forEach(f => f());
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

function addToggle(id) {
    const toggleState = () => state[id] = !state[id];
    const update = () => {
        toggle.style['background-color'] = state[id] ? 'green' : 'red';
        toggle.style['border-style'] = changeable(id) ? 'solid' : 'none';
    };
    let toggle = document.createElement('span');
    toggle.style.display = 'inline-block';
    toggle.style.width = '50px';
    toggle.style.height = '50px';
    toggle.style.margin = '5px';

    // border
    toggle.style['border-color'] = 'blue';
    toggle.style['border-width'] = '4px';

    update();
    toggle.onclick = event => {
        if(changeable(id)) {
            toggleState();
            updateAll();
        }
    };
    updates[id] = update;
    lock.appendChild(toggle);
}

for(let i = 0; i < SIZE; i++) {
    addToggle(i);
}

var tgl = lock.childNodes[0];

