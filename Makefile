#########################################
#     Custom MakeFile                   #
# By AJHL                  							#
#########################################


#============================================
# config
#============================================

OUTPUT_DIR = bin
ALGO_DIR = src

#============================================
# algorithm
#============================================
algorithm: 
	$(MAKE) -C $(ALGO_DIR)

now: algorithm

#============================================
# extra's
#============================================

setup:
	-mkdir witnesses
	-mkdir coverage

report:
	ocveralls --prefix coverage coverage/run*.out --send

test:
	@./test

clean:
	$(MAKE) clean -C $(ALGO_DIR)
	rm -fr witnesses/*


.PHONY: test setup compiler clean now
