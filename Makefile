IDRIS ?= idris2 
PACK ?= pack 
LIB_FILES := $(wildcard ./src/*.idr)
TEST_FILES := $(wildcard ./test/*.idr)
LIB_PKG := ./idris-mult.ipkg 
TEST_PKG := ./test/test.ipkg
TEST_EXEC := ./test/build/exec/idris-mult-test
all: clean build test docs install 

clean:
	@$(IDRIS) --clean $(LIB_PKG)
	@$(IDRIS) --clean $(TEST_PKG)

build: $(LIB_FILES) $(LIB_PKG)
	$(IDRIS) --build $(LIB_PKG)

install: build 
	$(IDRIS) --install $(LIB_PKG)

test: install $(TEST_PKG) $(TEST_FILES)
	$(IDRIS) --build $(TEST_PKG)	
	@$(TEST_EXEC) 

docs: $(LIB_PKG) $(LIB_FILES)
	$(IDRIS) --mkdoc $(LIB_PKG)
