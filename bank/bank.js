Object.entries(lock.children).forEach(([id, child]) => lock.removeChild(child));

var SIZE = 7;
var lock = document.getElementById('lock');

var state = [];
for(let i = 0; i < SIZE; i++) {
    state.push(false);
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

function createToggle(id) {
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
            update();
        }
    };
    return toggle;
}

for(let i = 0; i < SIZE; i++) {
    let toggle = createToggle(i);
    lock.appendChild(toggle);
}

var tgl = lock.childNodes[0];

