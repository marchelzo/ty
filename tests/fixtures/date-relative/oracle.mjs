import {createRequire} from 'node:module';
import {resolve} from 'node:path';

const require = createRequire(resolve(process.argv[2], 'package.json'));
const {Temporal: T} = require('@js-temporal/polyfill');
const units = ['year', 'month', 'week', 'day', 'hour', 'minute', 'second'];
const rows = [];
let seed = 20260916;

function random(n) {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed % n;
}

function words(duration, largest, parts) {
    const counts = units.map(unit => duration[`${unit}s`]);
    if (units.indexOf(largest) <= 2) {
        counts[2] += Math.trunc(counts[3] / 7);
        counts[3] %= 7;
    }
    return counts.flatMap((n, i) => n ? [`${n} ${units[i]}${n === 1 ? '' : 's'}`] : [])
        .slice(0, parts).join(', ');
}

function add(kind, a, b, zone = null, firstUnit = 'year') {
    const types = {
        date: T.PlainDate, plain: T.PlainDateTime,
        zoned: T.ZonedDateTime, instant: T.ZonedDateTime
    };
    const compare = types[kind].compare;
    if (compare(a, b) > 0) [a, b] = [b, a];
    const choices = units.slice(units.indexOf(firstUnit), kind === 'date' ? 4 : 7);
    for (const largest of choices) {
        const duration = a.until(b, {
            largestUnit: largest,
            smallestUnit: kind === 'date' ? 'day' : 'second',
            roundingMode: 'trunc'
        });
        for (const parts of [1, 2, 7]) {
            const text = words(duration, largest, parts);
            const empty = kind === 'date' ? 'today' : 'now';
            rows.push({
                kind, zone, largest, parts,
                a: kind === 'instant' ? String(a.epochNanoseconds) : String(a),
                b: kind === 'instant' ? String(b.epochNanoseconds) : String(b),
                past: text ? `${text} ago` : empty,
                future: text ? `in ${text}` : empty
            });
        }
    }
}

for (const year of [-400, -1, 0, 1, 1600, 1900, 1999, 2000, 2020, 2100, 2400]) {
    for (const month of [1, 2, 3, 8, 12]) {
        const first = T.PlainDate.from({year, month, day: 31}, {overflow: 'constrain'});
        for (const days of [1, 28, 29, 30, 59, 365, 366, 395]) {
            add('date', first, first.add({days}));
        }
    }
}

for (let i = 0; i < 100; i++) {
    const a = T.PlainDateTime.from({
        year: 1800 + random(500), month: 1 + random(12), day: 1 + random(28),
        hour: random(24), minute: random(60), second: random(60),
        millisecond: random(1000), microsecond: random(1000), nanosecond: random(1000)
    });
    add('plain', a, a.add({days: random(1600), seconds: random(86400)}));
}

const transitions = [
    ['America/New_York', '2024-03-10'], ['America/New_York', '2024-11-03'],
    ['Australia/Lord_Howe', '2024-04-07'], ['Australia/Lord_Howe', '2024-10-06'],
    ['Pacific/Apia', '2011-12-31'], ['Asia/Kathmandu', '1986-01-01'],
    ['America/Sao_Paulo', '2018-11-04'], ['Europe/London', '2024-10-27']
];

for (const [zone, day] of transitions) {
    for (const hour of [0, 1, 2, 3, 12, 23]) {
        const midnight = T.PlainDate.from(day).toZonedDateTime(zone);
        const a = midnight.add({hours: hour}).subtract({days: 31});
        for (const span of [1, 30, 31, 32, 365]) {
            const b = a.add({days: span}).add({minutes: random(121) - 60});
            add('zoned', a, b);
        }
    }
}

for (const [a, b] of [
    ['2024-11-03T01:30:00-04:00[America/New_York]',
     '2024-11-03T01:15:00-05:00[America/New_York]'],
    ['2024-11-03T01:30:00-05:00[America/New_York]',
     '2024-11-04T01:15:00-05:00[America/New_York]']
]) add('zoned', T.ZonedDateTime.from(a), T.ZonedDateTime.from(b), null, 'hour');

add('zoned',
    T.ZonedDateTime.from('2024-02-10T02:30:00-05:00[America/New_York]'),
    T.ZonedDateTime.from('2024-03-11T02:30:00-04:00[America/New_York]'));

for (const zone of ['UTC', '+23:59', '-23:59', 'America/New_York']) {
    const bounds = [-9223372036854775808n, -1n, 0n, 9223372036854775807n];
    for (let i = 0; i < bounds.length; i++) {
        for (let j = i; j < bounds.length; j++) {
            add('instant', new T.Instant(bounds[i]).toZonedDateTimeISO(zone),
                new T.Instant(bounds[j]).toZonedDateTimeISO(zone), zone);
        }
    }
}

process.stdout.write(JSON.stringify(rows));
