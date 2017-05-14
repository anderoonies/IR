all: L1_lang L2_lang L3_lang IR_lang

L1_lang:
	cd L1 ; make 

L2_lang:
	cd L2 ; make

L3_lang:
	cd L3 ; make

IR_lang:
	cd IR ; make

framework:
	./scripts/framework.sh

homework:
	./scripts/homework.sh

clean:
	rm -f *.bz2 ; cd L1 ; make clean ; cd ../L2 ; make clean ; cd ../L3 ; make clean ; cd ../IR ; make clean ; 
