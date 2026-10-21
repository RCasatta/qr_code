use crate::decode::{decode, BitGrid};
use bmp_monochrome::BmpError;

impl BitGrid for &bmp_monochrome::Bmp {
    fn size(&self) -> usize {
        self.width() as usize
    }

    fn bit(&self, y: usize, x: usize) -> bool {
        self.get(y as u16, x as u16)
    }
}

/// Allows to decode the QR coded in a bmp file
pub trait BmpDecode {
    /// Decode the QR code in a BMP, returning `BmpError::Data` for invalid QR data.
    fn decode(&self) -> Result<Vec<u8>, BmpError>;
}

impl BmpDecode for bmp_monochrome::Bmp {
    fn decode(&self) -> Result<Vec<u8>, BmpError> {
        if self.width() != self.height() {
            return Err(BmpError::Data);
        }

        let mut output = Vec::new();
        decode(&self, &mut output).map_err(|_| BmpError::Data)?;
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::BmpDecode;
    use crate::decode::decode::{
        codestream_ecc, decode_payload, read_data, read_format, MetaData, Version,
    };
    use crate::decode::BitGrid;
    use bmp_monochrome::Bmp;
    use std::fs::File;
    use std::io::Cursor;

    #[test]
    fn test_decode() {
        let bmp = &Bmp::read(File::open("test_data/test.bmp").unwrap()).unwrap();
        let meta = read_format(&bmp).unwrap();
        let expected = MetaData {
            version: Version(1),
            ecc_level: 0,
            mask: 2,
        };
        assert_eq!(&expected, &meta);

        let raw = read_data(&bmp, &meta);
        let stream = codestream_ecc(&meta, raw).unwrap();
        let mut writer = Cursor::new(vec![]);
        decode_payload(&meta, stream, &mut writer).unwrap();
        let out = String::from_utf8(writer.into_inner()).unwrap();
        assert_eq!("Hello", &out);
    }

    #[test]
    fn malformed_bmps_return_errors() {
        let too_small = Bmp::new(vec![vec![false]]).unwrap();
        assert!(too_small.decode().is_err());

        let not_square = Bmp::new(vec![vec![false; 21]; 20]).unwrap();
        assert!(not_square.decode().is_err());

        let corrupt = Bmp::new(vec![vec![false; 21]; 21]).unwrap();
        assert!(corrupt.decode().is_err());

        let valid = Bmp::read(File::open("test_data/test.bmp").unwrap()).unwrap();
        let damaged_rows = (0..valid.height())
            .map(|y| {
                (0..valid.width())
                    .map(|x| (x == 8 || y == 8) && valid.get(y, x))
                    .collect()
            })
            .collect();
        let damaged = Bmp::new(damaged_rows).unwrap();
        assert!(damaged.decode().is_err());
    }

    #[test]
    fn test_grid() {
        let expected = r#"
#######..####.#######
#.....#.....#.#.....#
#.###.#.#.#.#.#.###.#
#.###.#.#.#...#.###.#
#.###.#.##..#.#.###.#
#.....#.##.#..#.....#
#######.#.#.#.#######
........#.#..........
#.#####..#.#..#####..
...#....#..####..##.#
..#####..##.#.##.###.
..#..#.##.#####..##..
.###..#####.#..#....#
........#...#..#.#...
#######..#.#.#..#.##.
#.....#.#.#....#####.
#.###.#.#..#.#..#..#.
#.###.#.##.#####.#...
#.###.#.##..#.##..#..
#.....#..#.####.###..
#######.##..#...#..#.
"#;
        let mut chars = expected.chars();
        let bmp = &Bmp::read(File::open("test_data/test.bmp").unwrap()).unwrap();
        for i in 0..bmp.size() {
            for j in 0..bmp.size() {
                let mut char = chars.next().unwrap();
                if char == '\n' {
                    char = chars.next().unwrap();
                }
                assert_eq!(char == '#', bmp.bit(i, j));
            }
        }
    }
}
