{".rs", "@rust", 0, 1, 0},
{"@rust",
    "rust1 %i"
    " %{shared:-fcrate-type=cdylib}"
    " %{!shared:-fcrate-type=bin}"
    " %(cc1_options)"
    " %{!fsyntax-only:%(invoke_as)}",
    0, 1, 0},
