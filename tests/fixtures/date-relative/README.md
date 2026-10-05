# Temporal differential checks

From the repository root, install the reference implementation outside the source tree:

```sh
npm install --prefix /tmp/ty-date-temporal --ignore-scripts @js-temporal/polyfill@0.5.1
node tests/fixtures/date-relative/oracle.mjs /tmp/ty-date-temporal > /tmp/date-cases.json
./ty tests/fixtures/date-relative/check.ty /tmp/date-cases.json
./ty -j tests/fixtures/date-relative/check.ty /tmp/date-cases.json
```

The seeded generator produces 13,299 cases. Each is checked in both directions, using
one, two, and seven components across the available largest units. Cases cover leap
centuries, negative years, month ends, fractional seconds, timezone transitions,
half-hour shifts, skipped dates, historical offsets, and the signed 64-bit instant range.
JavaScript supplies Temporal arithmetic; the small English renderer only pluralizes,
splits remaining days into weeks, and joins components. Both runtimes need timezone data.
No JavaScript dependency is required for the normal Ty test suite.

Two New York repeated-hour cases use the polyfill only for hour-or-smaller units:

| Start | End | Elapsed time |
| --- | --- | --- |
| 2024-11-03 01:30 -04:00 | 2024-11-03 01:15 -05:00 | 45 minutes |
| 2024-11-03 01:30 -05:00 | 2024-11-04 01:15 -05:00 | 23 hours, 45 minutes |

With calendar units, polyfill 0.5.1 throws a mixed-sign-duration error for the first
and produces 24 hours, 45 minutes for the second. Neither interval completes a calendar
day. Ty preserves the supplied instants when the calendar portion is zero, so its
default output uses the elapsed times above. Both cases are independently asserted in
`tests/lib/date-relative.ty`; exceptions and disagreements are never silently skipped.
