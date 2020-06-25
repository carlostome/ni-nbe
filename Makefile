SRC=src
.PHONY: clean check

clean:
	find $(SRC) -iname '*.agdai' -exec rm "{}" \;

check:
	agda -i $(SRC) $(SRC)/Everything.agda
