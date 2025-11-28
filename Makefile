IDRIS ?= idris2 
PACK ?= pack 
IDRIS_OPTS ?= 
LIB_FILES := $(wildcard ./src/*.idr)
TEST_FILES := $(wildcard ./test/*.idr)
LIB_PKG := ./idris-mult.ipkg 
TEST_PKG := ./test/test.ipkg
TEST_EXEC := ./test/build/exec/idris-mult-test
all: clean build test docs install 

clean:
	@$(IDRIS) $(IDRIS_OPTS) --clean $(LIB_PKG)
	@$(IDRIS) $(IDRIS_OPTS) --clean $(TEST_PKG)

build: $(LIB_FILES) $(LIB_PKG)
	$(IDRIS) $(IDRIS_OPTS) --build $(LIB_PKG)

install: build 
	$(IDRIS) $(IDRIS_OPTS) --install $(LIB_PKG)

test: install $(TEST_PKG) $(TEST_FILES)
	$(IDRIS) $(IDRIS_OPTS) --build $(TEST_PKG)	
	@$(TEST_EXEC) 

docs: $(LIB_PKG) $(LIB_FILES)
	$(IDRIS) $(IDRIS_OPTS) --mkdoc $(LIB_PKG)
