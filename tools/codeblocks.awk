BEGIN {
    printThisLine = 0
}

{   if ($0 ~ /^```coq/) {
        printThisLine = 1
    } else if ($0 ~ /^```[:space:]*$/) {
        printThisLine = 0
        print ""
    } else {
        if (printThisLine) print $0
    }
}