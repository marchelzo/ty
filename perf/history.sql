PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS runs (
    id                  INTEGER PRIMARY KEY,
    recorded_at         TEXT NOT NULL,
    duration_seconds    REAL,
    runner              TEXT NOT NULL,
    mode                TEXT NOT NULL,
    build_config        TEXT NOT NULL,
    commit_hash         TEXT,
    branch              TEXT,
    dirty               INTEGER NOT NULL CHECK (dirty IN (0, 1)),
    dirty_file_count    INTEGER NOT NULL DEFAULT 0,
    dirty_files_json    TEXT NOT NULL DEFAULT '[]',
    machine_id          TEXT NOT NULL,
    machine_json        TEXT NOT NULL,
    suite_hash          TEXT NOT NULL,
    warmup              INTEGER NOT NULL,
    rounds              INTEGER NOT NULL,
    benchmark_filter    TEXT,
    benchmark_count     INTEGER NOT NULL,
    expected_count      INTEGER,
    full_suite          INTEGER NOT NULL CHECK (full_suite IN (0, 1)),
    auto_eligible       INTEGER NOT NULL CHECK (auto_eligible IN (0, 1)),
    eligibility_reason  TEXT NOT NULL,
    manual_eligible     INTEGER CHECK (manual_eligible IN (0, 1)),
    manual_reason       TEXT,
    baseline_reset      INTEGER NOT NULL DEFAULT 0 CHECK (baseline_reset IN (0, 1)),
    note                TEXT,
    command             TEXT
);

CREATE TABLE IF NOT EXISTS measurements (
    id                  INTEGER PRIMARY KEY,
    run_id              INTEGER NOT NULL REFERENCES runs(id) ON DELETE CASCADE,
    benchmark           TEXT NOT NULL,
    iterations          INTEGER NOT NULL,
    sample_count        INTEGER NOT NULL,
    mean_seconds        REAL NOT NULL,
    median_seconds      REAL NOT NULL,
    min_seconds         REAL NOT NULL,
    max_seconds         REAL NOT NULL,
    stddev_seconds      REAL NOT NULL,
    cv                  REAL NOT NULL,
    auto_valid          INTEGER NOT NULL CHECK (auto_valid IN (0, 1)),
    validity_reason     TEXT,
    manual_valid        INTEGER CHECK (manual_valid IN (0, 1)),
    manual_reason       TEXT,
    baseline_seconds    REAL,
    baseline_mad        REAL,
    baseline_run_count  INTEGER NOT NULL DEFAULT 0,
    change_ratio        REAL,
    significance_ratio  REAL,
    verdict             TEXT NOT NULL,
    UNIQUE (run_id, benchmark)
);

CREATE TABLE IF NOT EXISTS samples (
    measurement_id      INTEGER NOT NULL REFERENCES measurements(id) ON DELETE CASCADE,
    sample_index        INTEGER NOT NULL,
    seconds             REAL NOT NULL,
    PRIMARY KEY (measurement_id, sample_index)
);

CREATE INDEX IF NOT EXISTS runs_context_idx
    ON runs (runner, mode, machine_id, suite_hash, id DESC);
CREATE INDEX IF NOT EXISTS measurements_benchmark_idx
    ON measurements (benchmark, run_id DESC);
CREATE INDEX IF NOT EXISTS measurements_run_idx
    ON measurements (run_id);

PRAGMA user_version = 1;
