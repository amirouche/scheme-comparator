all:
	python3 -m http.server

helpers: helpers.js
	./node_modules/.bin/webpack
