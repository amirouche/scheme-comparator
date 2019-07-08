let ReactDOM = helpers.default.ReactDOM;
let h = helpers.default.h;

let container = document.getElementById('container');


document.recv = function() {
    let json = document.javascript;
    ReactDOM.render(
        translate(json),
        container,
    );
}

let send = function(event, identifier) {
    event.preventDefault();
    var msg = {
        "identifier": identifier,
        "event": {'target.value': event.target.value},
    };
    document.scheme = JSON.stringify(msg);
    document.resume();
}

let makeCallback = function(identifier) {
    return function(event) {
        return send(event, identifier);
    };
}

/* Translate json to `vnode` using `h` react helper */
let translate = function(json) {
    let options = json.options || {};
    for (let key in options) {
        if(key.startsWith('on')) {
            options[key] = makeCallback(options[key]);
        }
    }

    // recurse to translate children
    let children = json.children || [];
    children = children.map(function(child) {  // TODO: optimize with a for-loop
        if (child instanceof Object) {
            return translate(child);
        } else { // it's a string or a number
            return child;
        }
    });

    return h(json.tag, options, children);
}


// application

document.inbox = 0;


let chibi;

function start(program, args) {
    return Chibi({
        print: console.log,
        printErr: console.error,
        program: program,
        arguments: args
    });
}


fetch("main.scm").then(function(response) {
    response.text().then(function(main) {
        console.log("starting chibi scheme...");
        chibi = start(main, []);
    });
})
