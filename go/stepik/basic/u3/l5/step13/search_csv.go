package main

import (
	"archive/zip"
	"bytes"
	"encoding/csv"
	"fmt"
	"io"
	"log"
)

func main() {
	// Open a zip archive for reading
	r, err := zip.OpenReader("test/data/task.zip")
	if err != nil {
		log.Fatal(err)
	}
	defer r.Close()

	// Iterate through the files in the archive
	for _, f := range r.File {
		info := f.FileInfo()
		if info.IsDir() {
			continue
		}

		rc, err := f.Open()
		if err != nil {
			log.Fatal(err)
		}

		buf, err := io.ReadAll(rc)
		if err != nil {
			log.Fatal(err)
		}

		err = rc.Close()
		if err != nil {
			log.Fatal(err)
		}

		if len(buf) > 0 && buf[0] != 0 {
			fmt.Printf("File '%s' is not empty. Try to read it as a CSV file\n", f.Name)
			cr := csv.NewReader(bytes.NewBuffer(buf))
			xs, err := cr.ReadAll()
			if err != nil {
				log.Fatal(err)
			}

			fmt.Printf("Answer: %s\n", xs[4][2])
		}
	}
}
