all: beeSolver beeReader

beeSolver:
	swipl -G0 -T0 -L0 -f none -F none -g true -t \
	"['bSolver'],qsave_program('BumbleBEE',[stand_alone(true),goal(bSolver),toplevel(prolog),init_file(none),foreign(save)])"
	mv BumbleBEE ../BumbleBEE
	cp ../satsolver/pl-glucose4.so ../pl-satsolver.so

beeReader:
	swipl -G0 -T0 -L0 -f none -F none -g true -t \
	"['bSolReader'],qsave_program('BumbleSol',[stand_alone(true),goal(bSolReader),toplevel(prolog),init_file(none),foreign(save)])"
	mv BumbleSol ../BumbleSol
	
clean:
	rm -f ../BumbleBEE
	rm -f ../BumbleSol
