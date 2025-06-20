serve:
	python3 -m http.server

serve-test:
	python3 -m http.server 3000

open:
	open http://localhost:8000

test:
	cd specs/with_state_graphs && bash gen_state_graphs.sh