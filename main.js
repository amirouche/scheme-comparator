document.querySelector('#noscript').style.display = "none";
document.querySelector('#loading').style.display = "block";

let ReactDOM = helpers.default.ReactDOM;
let hyperscript = helpers.default.h;

let container = document.getElementById('container');

// xhr helper

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

let xhrInProgress = false;

let xhr = function(request) {
    // initiate async GET or POST request
    if (request[0] === "GET") {
        let path = request[1]
        request = new Request(path);
    } else if (request[0] === "POST") {
        let path = request[1]
        let body = JSON.stringify(request[2]);
        request = new Request(path, {"method": "POST", "body": body});
    }
    xhrInProgress = true;
    document.querySelector('#xhr').style.display = "block";
    fetch(request)
        .then(function(response) {
            return response.json();
        })
        .then(function(json) {
            if (xhrInProgress === true) {
                xhrInProgress = false;
                document.querySelector('#xhr').style.display = "none";
                // TODO: add response status
                // return the xhr response to Scheme
                document.scheme_inbox = JSON.stringify(["xhr", json]);
                document.resume();
            }
        });
}

// reactjs integration

let patch = function(json) {
    /* patch the DOM using `JSON` representation of the new DOM */
    ReactDOM.render(
        translate(json),
        container,
    );
}

let makeCallback = function(identifier) {
    return function(event) {
        // XXX: this will invalidate / cancel any in-progress xhr
        // call, hence any in-progress `update` already in progress
        // scheme side both the xhr and the update will be
        // abandonned. MAYBE it will leak something scheme side. It is
        // somekind of throttling.
        xhrInProgress = false;
        document.querySelector('#xhr').style.display = "none";

        /* send serialized DOM event as EVENT with IDENTIFIER to Scheme VM */
        event.preventDefault();
        var msg = {
            "identifier": identifier,
            "event": {'target.value': event.target.value},
        };
        document.scheme_inbox = JSON.stringify(["event", msg]);
        document.resume();
    };
}

let translate = function(json) {
    /* Translate json to `vnode` using `h` react helper */

    /* Create event handlers / callbacks */
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

    return hyperscript(json.tag, options, children);
}


// TODO: DOCUMENT
function loop () {
    let json = document.javascript_inbox;
    document.javascript_inbox = undefined;
    if (json !== undefined) {
        if (json[0] === 'patch') {
            patch(json[1]);
        } else if (json[0] === 'xhr') {
            xhr(json[1]);
        }
    }
    window.requestAnimationFrame(loop); // !
}

// start Chibi Scheme VM with main.scm

let chibi;

function run_chibi(program, args) {
    return Chibi({
        print: console.log,
        printErr: console.error,
        program: program,
        arguments: args
    });
}

fetch("main.scm").then(function(response) {
    console.log("main.scm loaded...")
    response.text().then(function(main) {
        document.javascript_inbox = undefined;
        window.requestAnimationFrame(loop); // !
        console.log("starting Chibi Scheme...");
        chibi = run_chibi(main, []);
    });
})
