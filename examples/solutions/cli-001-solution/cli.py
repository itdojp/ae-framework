#!/usr/bin/env python3
"""
File Processing CLI Tool (CLI-001)
Converts between CSV, JSON, and TXT file formats.
"""

import argparse
import json
import csv
import os
import sys
from pathlib import Path
from typing import List, Dict, Any, Optional
import logging


class FileProcessor:
    """Core file processing functionality."""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.setup_logging()
    
    def setup_logging(self):
        """Setup logging based on verbose flag."""
        level = logging.DEBUG if self.verbose else logging.INFO
        logging.basicConfig(
            level=level,
            format='%(asctime)s - %(levelname)s - %(message)s'
        )
        self.logger = logging.getLogger(__name__)
    
    def validate_input_file(self, file_path: str) -> bool:
        """Validate input file existence and readability."""
        if not os.path.exists(file_path):
            self.logger.error(f"Input file does not exist: {file_path}")
            return False
        
        if not os.access(file_path, os.R_OK):
            self.logger.error(f"Input file is not readable: {file_path}")
            return False
        
        self.logger.debug(f"Input file validation passed: {file_path}")
        return True
    
    def detect_file_format(self, file_path: str) -> str:
        """Detect file format based on extension."""
        ext = Path(file_path).suffix.lower()
        format_map = {
            '.csv': 'csv',
            '.json': 'json',
            '.txt': 'txt'
        }
        return format_map.get(ext, 'unknown')
    
    def read_csv(self, file_path: str) -> List[Dict[str, Any]]:
        """Read CSV file and return list of dictionaries."""
        self.logger.debug(f"Reading CSV file: {file_path}")
        data = []
        with open(file_path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                data.append(row)
        return data
    
    def read_json(self, file_path: str) -> List[Dict[str, Any]]:
        """Read JSON file."""
        self.logger.debug(f"Reading JSON file: {file_path}")
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        if isinstance(data, list):
            return data
        elif isinstance(data, dict):
            return [data]
        else:
            raise ValueError("JSON must contain a list or dictionary")
    
    def read_txt(self, file_path: str) -> List[Dict[str, Any]]:
        """Read TXT file (line-based data)."""
        self.logger.debug(f"Reading TXT file: {file_path}")
        data = []
        with open(file_path, 'r', encoding='utf-8') as f:
            for i, line in enumerate(f, 1):
                line = line.strip()
                if line:
                    data.append({'line_number': i, 'content': line})
        return data
    
    def write_csv(self, data: List[Dict[str, Any]], file_path: str):
        """Write data to CSV file."""
        self.logger.debug(f"Writing CSV file: {file_path}")
        if not data:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write('')
            return
        
        fieldnames = data[0].keys()
        with open(file_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(data)
    
    def write_json(self, data: List[Dict[str, Any]], file_path: str):
        """Write data to JSON file."""
        self.logger.debug(f"Writing JSON file: {file_path}")
        with open(file_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    
    def write_txt(self, data: List[Dict[str, Any]], file_path: str):
        """Write data to TXT file."""
        self.logger.debug(f"Writing TXT file: {file_path}")
        with open(file_path, 'w', encoding='utf-8') as f:
            for item in data:
                if 'content' in item:
                    f.write(f"{item['content']}\n")
                elif 'line' in item:
                    f.write(f"{item['line']}\n")
                else:
                    # Convert dict to string representation
                    f.write(f"{str(item)}\n")
    
    def convert_file(self, input_path: str, output_path: str) -> bool:
        """Convert file from one format to another."""
        try:
            # Validate input file
            if not self.validate_input_file(input_path):
                return False
            
            # Detect input and output formats
            input_format = self.detect_file_format(input_path)
            output_format = self.detect_file_format(output_path)
            
            if input_format == 'unknown':
                self.logger.error(f"Unsupported input format: {input_path}")
                return False
            
            if output_format == 'unknown':
                self.logger.error(f"Unsupported output format: {output_path}")
                return False
            
            self.logger.info(f"Converting {input_format.upper()} to {output_format.upper()}: {input_path} -> {output_path}")
            
            # Read input file
            if input_format == 'csv':
                data = self.read_csv(input_path)
            elif input_format == 'json':
                data = self.read_json(input_path)
            elif input_format == 'txt':
                data = self.read_txt(input_path)
            
            # Ensure output directory exists
            output_dir = os.path.dirname(output_path)
            if output_dir:
                os.makedirs(output_dir, exist_ok=True)
            
            # Write output file
            if output_format == 'csv':
                self.write_csv(data, output_path)
            elif output_format == 'json':
                self.write_json(data, output_path)
            elif output_format == 'txt':
                self.write_txt(data, output_path)
            
            self.logger.info(f"Successfully converted: {input_path} -> {output_path}")
            return True
            
        except Exception as e:
            self.logger.error(f"Error converting {input_path} to {output_path}: {str(e)}")
            return False
    
    def get_file_info(self, file_path: str) -> Dict[str, Any]:
        """Get information about a file."""
        info = {
            'path': file_path,
            'format': self.detect_file_format(file_path),
            'size': os.path.getsize(file_path),
            'exists': os.path.exists(file_path),
            'readable': os.access(file_path, os.R_OK) if os.path.exists(file_path) else False
        }
        
        if info['readable']:
            try:
                if info['format'] == 'csv':
                    data = self.read_csv(file_path)
                elif info['format'] == 'json':
                    data = self.read_json(file_path)
                elif info['format'] == 'txt':
                    data = self.read_txt(file_path)
                else:
                    data = []
                
                info['records'] = len(data)
                if data:
                    info['fields'] = list(data[0].keys())
                else:
                    info['fields'] = []
                    
            except Exception as e:
                info['error'] = str(e)
        
        return info


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description='File Processing CLI Tool - Convert between CSV, JSON, and TXT formats',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s convert data.csv data.json
  %(prog)s convert data.json data.txt --verbose
  %(prog)s batch *.csv --output-dir converted --format json
  %(prog)s info data.csv
        """
    )
    parser.add_argument('--version', action='version', version='%(prog)s 1.0.0')
    
    subparsers = parser.add_subparsers(dest='command', help='Available commands')
    
    # Convert command
    convert_parser = subparsers.add_parser('convert', help='Convert a single file')
    convert_parser.add_argument('input_file', help='Input file path')
    convert_parser.add_argument('output_file', help='Output file path')
    convert_parser.add_argument('--verbose', '-v', action='store_true', 
                               help='Enable verbose output')
    
    # Batch command
    batch_parser = subparsers.add_parser('batch', help='Batch convert multiple files')
    batch_parser.add_argument('input_files', nargs='+', help='Input file paths')
    batch_parser.add_argument('--output-dir', '-o', required=True,
                             help='Output directory')
    batch_parser.add_argument('--format', '-f', required=True,
                             choices=['csv', 'json', 'txt'],
                             help='Target output format')
    batch_parser.add_argument('--verbose', '-v', action='store_true',
                             help='Enable verbose output')
    batch_parser.add_argument('--progress', '-p', action='store_true',
                             help='Show progress (basic counter)')
    
    # Info command
    info_parser = subparsers.add_parser('info', help='Display file information')
    info_parser.add_argument('file_path', help='File path to analyze')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return 1
    
    if args.command == 'convert':
        processor = FileProcessor(verbose=args.verbose)
        
        if processor.convert_file(args.input_file, args.output_file):
            print(f"✅ Successfully converted: {args.input_file} -> {args.output_file}")
            return 0
        else:
            print(f"❌ Failed to convert: {args.input_file} -> {args.output_file}")
            return 1
    
    elif args.command == 'batch':
        processor = FileProcessor(verbose=args.verbose)
        
        # Create output directory
        os.makedirs(args.output_dir, exist_ok=True)
        
        successful = 0
        failed = 0
        total = len(args.input_files)
        
        for i, input_file in enumerate(args.input_files, 1):
            if args.progress:
                print(f"Processing {i}/{total}: {input_file}")
            
            input_name = Path(input_file).stem
            output_file = os.path.join(args.output_dir, f"{input_name}.{args.format}")
            
            if processor.convert_file(input_file, output_file):
                successful += 1
            else:
                failed += 1
        
        print(f"\n📊 Batch conversion completed:")
        print(f"   ✅ Successful: {successful}")
        print(f"   ❌ Failed: {failed}")
        print(f"   📁 Output directory: {args.output_dir}")
        
        return 1 if failed > 0 else 0
    
    elif args.command == 'info':
        processor = FileProcessor(verbose=False)
        info = processor.get_file_info(args.file_path)
        
        print(f"📄 File Information:")
        print(f"   Path: {info['path']}")
        print(f"   Format: {info['format'].upper()}")
        print(f"   Size: {info['size']:,} bytes")
        print(f"   Exists: {'Yes' if info['exists'] else 'No'}")
        print(f"   Readable: {'Yes' if info['readable'] else 'No'}")
        
        if 'records' in info:
            print(f"   Records: {info['records']:,}")
            print(f"   Fields: {info['fields']}")
        
        if 'error' in info:
            print(f"   Error: {info['error']}")
        
        return 0


if __name__ == '__main__':
    sys.exit(main())