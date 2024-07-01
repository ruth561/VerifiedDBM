// #![feature(proc_macro_hygiene)]
// #![feature(stmt_expr_attributes)]

mod dbm;
mod down;
mod up;
mod free;
mod reset;

use creusot_contracts::*;
use textplots::{Chart, Plot, Shape};

use crate::dbm::*;

const BOUND: i64 = 100000; // 各制約の値はこの値を超えることはない。
const INF: i64 = i64::MAX; // 無限を表す値
const MAX_NODE: usize = 100000; // グラフの最大ノード数

const XIDX: usize = 1; // テストケース用
const YIDX: usize = 2; // テストケース用

#[trusted] // trustedをつけるとビルドエラーがでなくなる
fn print_dbm(dbm: &Vec<Vec<i64>>) {
    println!("=== print_dbm ===");
    for row in dbm {
        print!("[ ");
        for elem in row {
            if *elem == INF {
                print!("INF, ");
            } else {
                print!("{:3}, ", elem);
            }
        }
        println!("]");
    }
}

// 3変数のケースのみに対応
// x, y in [-1.0, 6.0]の範囲の領域を図示する
#[trusted]
#[requires(dbm@.len() == 3)]
#[requires(is_canonical(dbm.deep_model(), dbm@.len()))]
fn print_clock_region(dbm: &Vec<Vec<i64>>) {

    let mut data = Vec::new();
    for x in -10..60 {
        for y in -10..60 {
            if 0 - x <= dbm[0][XIDX] &&
               0 - y <= dbm[0][YIDX] &&
               x - 0 <= dbm[XIDX][0] &&
               y - 0 <= dbm[YIDX][0] &&
               x - y <= dbm[XIDX][YIDX] &&
               y - x <= dbm[YIDX][XIDX] {
                data.push((x as f32, y as f32));
            }
        }
    }

    println!("\n============== CLOCK REGION ==============\n");
    Chart::new_with_y_range(70, 70, -10.0, 60.0, -10.0, 60.0)
        .lineplot(&Shape::Points(&data))
        .display();
}

#[trusted]
fn main() {
    let mut dbm = get_dbm();
    let n = dbm.len();
    print_dbm(&dbm);
    println!("This is DBM ? {}", check_is_dbm(&dbm));
    println!("This is canonical form DBM ? {}", check_is_canonical(&dbm));

    if check_is_canonical(&dbm) {
        print_clock_region(&dbm);
    }

    let mut rl = rustyline::DefaultEditor::new().unwrap();
    loop {
        print_dbm(&dbm);
        print_clock_region(&dbm);
        println!("");
        println!(" 1. up");
        println!(" 2. down");
        println!(" 3. free");
        println!(" 4. reset");
        println!(" q. exit");
        println!("");
        match rl.readline("> ") {
            Ok(s) => {
                if &s == "1" {
                    println!("[*] UP");
                    up::up(&mut dbm, n);
                } else if &s == "2" {
                    println!("[*] DOWN");
                    down::down(&mut dbm, n);
                } else if &s == "3 x" {
                    println!("[*] FREE x");
                    free::free(&mut dbm, n, XIDX);
                } else if &s == "3 y" {
                    println!("[*] FREE y");
                    free::free(&mut dbm, n, YIDX);
                } else if &s[0..3] == "4 x" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET x {m}");
                        reset::reset(&mut dbm, n, XIDX, m);
                    } else {
                        println!("failed to parse int.");
                    }
                } else if &s[0..3] == "4 y" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET y {m}");
                        reset::reset(&mut dbm, n, YIDX, m);
                    } else {
                        println!("failed to parse int.");
                    }
                } else if &s == "q" {
                    println!("Exit..");
                    break;
                } else {
                    println!("Invalid input: {s}");
                }
            },
            Err(_) => println!("No input"),
        }

    }
}
