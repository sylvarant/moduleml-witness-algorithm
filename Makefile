#########################################
#     Custom MakeFile                   #
# By AJHL                  #
#########################################

OUTPUT_DIR = bin
COMPILER_DIR = src
COMPILER_BIN = main.native


#============================================
# compiler
#============================================
compiler: 
	$(MAKE) -C $(COMPILER_DIR)

now: compiler

#============================================
# extra's
#============================================

setup:
	-mkdir witnesses

test:
	@./test

clean:
	$(MAKE) clean -C $(COMPILER_DIR)
	rm -fr witnesses/*


.PHONY: test setup compiler clean now
