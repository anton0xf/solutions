#!/bin/sh
{
    echo 'strict graph {'
    echo 'node [shape=plain]'
    <input sed 's/-/ -- /'
    echo '}'
} | dot -Tsvg -o graph.svg -K fdp
