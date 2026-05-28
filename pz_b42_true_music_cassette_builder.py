#!/usr/bin/env python3
"""
Project Zomboid Build 42 cassette-only music-pack builder for PZ True Music.

What it does:
- scans mp3/flac/wav/m4a/aac/opus/ogg recursively;
- groups tracks into albums by folder, top folder, root, or tags;
- converts/copies audio into the mod folder as OGG/Vorbis;
- skips conversion/copy if the target .ogg already exists;
- generates PZ True Music cassette items;
- generates GlobalMusic registrations, sound scripts, translations, loot spawn, and manifest.csv;
- does NOT generate CD disks at all.

Default local layout:
  OUT_DIR/MOD_ID/common/
  OUT_DIR/MOD_ID/42/mod.info
  OUT_DIR/MOD_ID/42/media/...

Workshop layout with --workshop-layout:
  OUT_DIR/MOD_ID/Contents/mods/MOD_ID/common/
  OUT_DIR/MOD_ID/Contents/mods/MOD_ID/42/...
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import locale
import os
import re
import textwrap
import shutil
import subprocess
import sys
import unicodedata
import zipfile
from dataclasses import dataclass, field
from pathlib import Path

AUDIO_EXTS = {".mp3", ".flac", ".wav", ".m4a", ".aac", ".ogg", ".opus"}

RU_MAP = str.maketrans({
    "а": "a", "б": "b", "в": "v", "г": "g", "д": "d", "е": "e", "ё": "e", "ж": "zh",
    "з": "z", "и": "i", "й": "y", "к": "k", "л": "l", "м": "m", "н": "n", "о": "o",
    "п": "p", "р": "r", "с": "s", "т": "t", "у": "u", "ф": "f", "х": "h", "ц": "ts",
    "ч": "ch", "ш": "sh", "щ": "sch", "ъ": "", "ы": "y", "ь": "", "э": "e", "ю": "yu", "я": "ya",
    "А": "A", "Б": "B", "В": "V", "Г": "G", "Д": "D", "Е": "E", "Ё": "E", "Ж": "Zh",
    "З": "Z", "И": "I", "Й": "Y", "К": "K", "Л": "L", "М": "M", "Н": "N", "О": "O",
    "П": "P", "Р": "R", "С": "S", "Т": "T", "У": "U", "Ф": "F", "Х": "H", "Ц": "Ts",
    "Ч": "Ch", "Ш": "Sh", "Щ": "Sch", "Ъ": "", "Ы": "Y", "Ь": "", "Э": "E", "Ю": "Yu", "Я": "Ya",
})

DIST_NAMES = [
    "ArmyStorageElectronics", "BandPracticeInstruments", "BedroomDresser", "BedroomSidetable",
    "BinBar", "ClassroomDesk", "ClassroomMisc", "ClosetShelfGeneric", "CrateCamping",
    "CrateCompactDiscs", "CrateElectronics", "CrateRandomJunk", "DeskGeneric", "DresserGeneric",
    "ElectronicStoreMisc", "ElectronicStoreMusic", "FactoryLockers", "FireDeptLockers", "GarageTools",
    "GigamartHouseElectronics", "GymLockers", "JanitorMisc", "KitchenRandom", "LibraryCounter",
    "LivingRoomShelf", "LivingRoomShelfNoTapes", "LockerClassy", "Locker", "MusicStoreCDs",
    "MusicStoreOthers", "MusicStoreSpeaker", "OfficeCounter", "OfficeDesk", "OfficeDeskHome",
    "OfficeDeskHomeClassy", "OfficeDeskSecretary", "OfficeDeskStressed", "OfficeDrawers",
    "OfficeShelfSupplies", "PoliceDesk", "PoliceLockers", "ShelfGeneric", "StoreShelfElectronics",
    "SchoolLockers", "UniversityDesk_Music", "WardrobeChild", "WardrobeClassy", "WardrobeGeneric",
    "WardrobeRedneck",
]

VEHICLE_DIST_NAMES = ["GloveBox", "SeatRearLeft", "SeatRearRight"]


TRUE_MUSIC_LANGS = [
    "EN", "AR", "CA", "CH", "CN", "CS", "DA", "DE", "ES", "FI", "FR", "HU", "ID", "IT",
    "JP", "KO", "NL", "NO", "PH", "PL", "PT", "PTBR", "RO", "RU", "TH", "TR", "UA",
]

LANG_DISPLAY_NAMES = {
    "EN": "English",
    "AR": "Espanol (AR)",
    "CA": "Catalan",
    "CH": "Traditional Chinese",
    "CN": "Simplified Chinese",
    "CS": "Czech",
    "DA": "Danish",
    "DE": "Deutsch",
    "ES": "Espanol (ES)",
    "FI": "Finnish",
    "FR": "Francais",
    "HU": "Hungarian",
    "ID": "Indonesia",
    "IT": "Italiano",
    "JP": "Japanese",
    "KO": "Korean",
    "NL": "Nederlands",
    "NO": "Norsk",
    "PH": "Tagalog",
    "PL": "Polish",
    "PT": "Portuguese",
    "PTBR": "Brazilian Portuguese",
    "RO": "Romanian",
    "RU": "Russian",
    "TH": "Thai",
    "TR": "Türkish",
    "UA": "Ukrainian",
}

CASSETTE_WORD = {
    "EN": "Cassette", "AR": "Casete", "CA": "Casset", "CH": "卡帶", "CN": "磁带",
    "CS": "Kazeta", "DA": "Kassette", "DE": "Kassette", "ES": "Casete", "FI": "Kasetti",
    "FR": "Cassette", "HU": "Kazetta", "ID": "Kaset", "IT": "Cassetta", "JP": "カセット",
    "KO": "카세트", "NL": "Cassette", "NO": "Kassett", "PH": "Cassette", "PL": "Kaseta",
    "PT": "Cassete", "PTBR": "Cassete", "RO": "Casetă", "RU": "Кассета", "TH": "เทปคาสเซ็ต",
    "TR": "Kaset", "UA": "Касета",
}

SPAWN_CHANCE_TEXT = {
    "EN": "Default spawn chance", "AR": "Probabilidad de aparición, predeterminado",
    "CA": "Probabilitat d'aparició, per defecte", "CH": "生成機率，預設", "CN": "生成几率，默认",
    "CS": "Šance výskytu, výchozí", "DA": "Spawnchance, standard", "DE": "Spawn-Chance, Standard",
    "ES": "Probabilidad de aparición, predeterminado", "FI": "Ilmestymisen todennäköisyys, oletus",
    "FR": "Chance d'apparition, par défaut", "HU": "Megjelenési esély, alapértelmezett",
    "ID": "Peluang muncul, default", "IT": "Probabilità di spawn, predefinito", "JP": "出現率、既定",
    "KO": "스폰 확률, 기본값", "NL": "Spawnkans, standaard", "NO": "Spawn-sjanse, standard",
    "PH": "Tsansa ng spawn, default", "PL": "Szansa pojawienia, domyślnie", "PT": "Chance de aparecimento padrão",
    "PTBR": "Chance de aparecimento, padrão", "RO": "Șansă de apariție, implicit", "RU": "Шанс появления по умолчанию",
    "TH": "โอกาสเกิด ค่าเริ่มต้น", "TR": "Çıkma şansı, varsayılan", "UA": "Шанс появи типово",
}

SPAWN_ALBUM_TEXT = {
    "EN": "Spawn album", "AR": "Generar álbum", "CA": "Generar àlbum", "CH": "生成專輯", "CN": "生成专辑",
    "CS": "Výskyt alba", "DA": "Spawn album", "DE": "Album spawnen", "ES": "Generar álbum",
    "FI": "Luo albumi", "FR": "Faire apparaître l'album", "HU": "Album megjelenése", "ID": "Munculkan album",
    "IT": "Genera album", "JP": "アルバムを出現", "KO": "앨범 스폰", "NL": "Album spawnen", "NO": "Spawn album",
    "PH": "Spawn album", "PL": "Pojawianie albumu", "PT": "Gerar álbum", "PTBR": "Gerar álbum",
    "RO": "Generează albumul", "RU": "Спавн альбома", "TH": "สร้างอัลบั้ม", "TR": "Albüm çıkar",
    "UA": "Спавн альбому",
}

HELP_TRANSLATIONS = {
    "EN": {
        "usage": "Usage",
        "description": "Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.",
        "required": "Required arguments",
        "optional": "Options",
        "examples": "Examples",
        "input": "Folder with mp3/flac/wav/m4a/aac/ogg/opus files.",
        "output": "Output folder for the generated mod. Default: ./build.",
        "mod_id": "Technical mod ID. Non-ASCII characters are sanitized automatically.",
        "name": "Mod name shown in the game menu.",
        "author": "Author name. Default: Average User.",
        "album_name": "Album name used with --album-mode root or for tracks in the input root.",
        "album_mode": "How tracks are grouped into albums: leaf-folder, top-folder, root, tags.",
        "use_tags": "Read title/artist/genre from metadata through ffprobe.",
        "manifest_csv": "CSV override with columns: file,title,artist,album,genre.",
        "max_tracks_per_album": "Split huge albums into parts. 0 disables splitting. Default: 180.",
        "modversion": "Mod version written to mod.info. Default: 1.0.",
        "require_mod": "require= value in mod.info. For PZ True Music use truemusic. Empty string disables it.",
        "spawn": "Sandbox spawn value. 5 = 0.5 loot weight. For huge packs use 1..10.",
        "quality": "OGG/Vorbis quality for ffmpeg: 0..10. Usually 4 or 5 is enough.",
        "copy_ogg": "Copy source .ogg files without re-encoding.",
        "rebuild_audio": "Reconvert/recopy .ogg even if target files already exist.",
        "skip_audio": "Do not convert/copy audio, generate only text/script files.",
        "languages": "Translation folders to generate. Default: all PZ True Music languages plus EN.",
        "workshop_layout": "Build in Steam Workshop layout: Contents/mods/MOD_ID.",
        "make_zip": "Also create a zip archive.",
        "dry_run": "Only show detected albums/tracks; do not build anything.",
        "force": "Update existing mod and keep already converted .ogg files.",
        "reset": "Delete existing mod folder completely, including .ogg files.",
        "help": "Show this help and exit.",
        "help_lang": "Force help language. Codes: EN, RU, DE, ES, PTBR, etc.",
        "example1": "Fast build from already converted OGG files:",
        "example2": "Show <LANG> help explicitly:",
    },
    "RU": {
        "usage": "Использование",
        "description": "Собирает music-pack только с кассетами для Project Zomboid Build 42 и PZ True Music.",
        "required": "Обязательные параметры",
        "optional": "Параметры",
        "examples": "Примеры",
        "input": "Папка с файлами mp3/flac/wav/m4a/aac/ogg/opus.",
        "output": "Куда собрать мод. По умолчанию: ./build.",
        "mod_id": "Технический ID мода. Кириллица и опасные символы очищаются автоматически.",
        "name": "Название мода в игровом меню.",
        "author": "Автор. По умолчанию: Average User.",
        "album_name": "Название альбома для --album-mode root или треков прямо в корне папки.",
        "album_mode": "Как делить треки на альбомы: leaf-folder, top-folder, root, tags.",
        "use_tags": "Читать title/artist/genre из метаданных через ffprobe.",
        "manifest_csv": "CSV для ручной правки с колонками: file,title,artist,album,genre.",
        "max_tracks_per_album": "Делить огромные альбомы на части. 0 = не делить. По умолчанию: 180.",
        "modversion": "Версия мода для mod.info. По умолчанию: 1.0.",
        "require_mod": "Строка require= в mod.info. Для PZ True Music обычно truemusic. Пустая строка отключает.",
        "spawn": "Значение спавна в sandbox. 5 = 0.5 веса лута. Для больших паков лучше 1..10.",
        "quality": "Качество OGG/Vorbis для ffmpeg: 0..10. Обычно хватает 4 или 5.",
        "copy_ogg": "Копировать исходные .ogg без повторного перекодирования.",
        "rebuild_audio": "Переконвертировать/перекопировать .ogg даже если целевые файлы уже существуют.",
        "skip_audio": "Не конвертировать и не копировать аудио, только сгенерировать текстовые файлы.",
        "languages": "Папки переводов для генерации. По умолчанию: все языки PZ True Music плюс EN.",
        "workshop_layout": "Собрать в формате Steam Workshop: Contents/mods/MOD_ID.",
        "make_zip": "Дополнительно создать zip-архив.",
        "dry_run": "Только показать найденные альбомы и треки, ничего не собирать.",
        "force": "Обновить существующий мод и сохранить уже сконвертированные .ogg.",
        "reset": "Полностью удалить существующую папку мода, включая .ogg.",
        "help": "Показать эту справку и выйти.",
        "help_lang": "Принудительно выбрать язык справки. Коды: EN, RU, DE, ES, PTBR и т.д.",
        "example1": "Быстрая сборка из уже сконвертированных OGG:",
        "example2": "Явно показать справку на другом языке:",
    },
    "DE": {
        "usage": "Verwendung", "description": "Erstellt ein reines Kassetten-Musikpaket für Project Zomboid Build 42 und PZ True Music.",
        "required": "Pflichtargumente", "optional": "Optionen", "examples": "Beispiele",
        "input": "Ordner mit mp3/flac/wav/m4a/aac/ogg/opus-Dateien.", "output": "Ausgabeordner für den Mod. Standard: ./build.",
        "mod_id": "Technische Mod-ID. Nicht-ASCII-Zeichen werden automatisch bereinigt.", "name": "Mod-Name im Spielmenü.",
        "author": "Autor. Standard: Average User.", "album_name": "Albumname für --album-mode root oder Dateien im Stammordner.",
        "album_mode": "Gruppierung der Titel: leaf-folder, top-folder, root, tags.", "use_tags": "title/artist/genre aus Metadaten per ffprobe lesen.",
        "manifest_csv": "CSV mit Spalten: file,title,artist,album,genre.", "max_tracks_per_album": "Große Alben teilen. 0 deaktiviert. Standard: 180.",
        "modversion": "Mod-Version für mod.info. Standard: 1.0.", "require_mod": "require= in mod.info. Für PZ True Music meist truemusic. Leer deaktiviert.",
        "spawn": "Sandbox-Spawnwert. 5 = 0.5 Loot-Gewicht. Für große Pakete 1..10.", "quality": "OGG/Vorbis-Qualität für ffmpeg: 0..10. Meist 4 oder 5.",
        "copy_ogg": "Vorhandene .ogg ohne Neukodierung kopieren.", "rebuild_audio": "Audio auch bei vorhandenen Zieldateien neu erstellen.",
        "skip_audio": "Audio nicht kopieren/konvertieren, nur Textdateien erzeugen.", "languages": "Zu erzeugende Übersetzungsordner. Standard: alle PZ True Music-Sprachen plus EN.",
        "workshop_layout": "Steam-Workshop-Layout bauen: Contents/mods/MOD_ID.", "make_zip": "Zusätzlich ein zip-Archiv erstellen.",
        "dry_run": "Nur erkannte Alben/Titel anzeigen, nichts bauen.", "force": "Vorhandenen Mod aktualisieren und konvertierte .ogg behalten.",
        "reset": "Vorhandenen Mod-Ordner komplett löschen, inklusive .ogg.", "help": "Diese Hilfe anzeigen und beenden.",
        "help_lang": "Hilfesprache erzwingen. Codes: EN, RU, DE, ES, PTBR usw.", "example1": "Schneller Build aus vorhandenen OGG-Dateien:", "example2": "Hilfe explizit auf Deutsch anzeigen:",
    },
    "ES": {
        "usage": "Uso", "description": "Crea un paquete de música solo con casetes para Project Zomboid Build 42 y PZ True Music.",
        "required": "Argumentos obligatorios", "optional": "Opciones", "examples": "Ejemplos",
        "input": "Carpeta con archivos mp3/flac/wav/m4a/aac/ogg/opus.", "output": "Carpeta de salida del mod. Predeterminado: ./build.",
        "mod_id": "ID técnico del mod. Los caracteres no ASCII se limpian automáticamente.", "name": "Nombre del mod en el menú del juego.",
        "author": "Autor. Predeterminado: Average User.", "album_name": "Nombre de álbum para --album-mode root o pistas en la raíz.",
        "album_mode": "Cómo agrupar pistas: leaf-folder, top-folder, root, tags.", "use_tags": "Leer title/artist/genre desde metadatos con ffprobe.",
        "manifest_csv": "CSV con columnas: file,title,artist,album,genre.", "max_tracks_per_album": "Dividir álbumes grandes. 0 desactiva. Predeterminado: 180.",
        "modversion": "Versión del mod para mod.info. Predeterminado: 1.0.", "require_mod": "Valor require= en mod.info. Para PZ True Music normalmente truemusic. Vacío lo desactiva.",
        "spawn": "Valor de aparición en sandbox. 5 = 0.5 de peso de loot. Para paquetes grandes usa 1..10.", "quality": "Calidad OGG/Vorbis para ffmpeg: 0..10. Normalmente 4 o 5.",
        "copy_ogg": "Copiar .ogg originales sin recodificar.", "rebuild_audio": "Reconvertir/recopiar aunque el .ogg destino ya exista.",
        "skip_audio": "No convertir/copiar audio, solo generar archivos de texto.", "languages": "Carpetas de traducción. Predeterminado: todos los idiomas de PZ True Music más EN.",
        "workshop_layout": "Construir con layout de Steam Workshop: Contents/mods/MOD_ID.", "make_zip": "Crear también un zip.",
        "dry_run": "Solo mostrar álbumes/pistas detectados; no construir.", "force": "Actualizar mod existente conservando .ogg ya convertidos.",
        "reset": "Borrar por completo el mod existente, incluidos .ogg.", "help": "Mostrar esta ayuda y salir.",
        "help_lang": "Forzar idioma de ayuda. Códigos: EN, RU, DE, ES, PTBR, etc.", "example1": "Construcción rápida desde OGG ya convertidos:", "example2": "Mostrar ayuda en español explícitamente:",
    },
    "PTBR": {
        "usage": "Uso", "description": "Cria um pacote de música somente com fitas cassete para Project Zomboid Build 42 e PZ True Music.",
        "required": "Argumentos obrigatórios", "optional": "Opções", "examples": "Exemplos",
        "input": "Pasta com arquivos mp3/flac/wav/m4a/aac/ogg/opus.", "output": "Pasta de saída do mod. Padrão: ./build.",
        "mod_id": "ID técnico do mod. Caracteres não ASCII são limpos automaticamente.", "name": "Nome do mod no menu do jogo.",
        "author": "Autor. Padrão: Average User.", "album_name": "Nome do álbum para --album-mode root ou faixas na raiz.",
        "album_mode": "Como agrupar faixas: leaf-folder, top-folder, root, tags.", "use_tags": "Ler title/artist/genre dos metadados com ffprobe.",
        "manifest_csv": "CSV com colunas: file,title,artist,album,genre.", "max_tracks_per_album": "Dividir álbuns grandes. 0 desativa. Padrão: 180.",
        "modversion": "Versão do mod em mod.info. Padrão: 1.0.", "require_mod": "Valor require= em mod.info. Para PZ True Music normalmente truemusic. Vazio desativa.",
        "spawn": "Valor de spawn no sandbox. 5 = 0.5 de peso de loot. Para pacotes grandes use 1..10.", "quality": "Qualidade OGG/Vorbis para ffmpeg: 0..10. Normalmente 4 ou 5.",
        "copy_ogg": "Copiar .ogg originais sem recodificar.", "rebuild_audio": "Reconverter/recopiar mesmo se o .ogg de destino existir.",
        "skip_audio": "Não converter/copiar áudio, apenas gerar arquivos de texto.", "languages": "Pastas de tradução. Padrão: todos os idiomas do PZ True Music mais EN.",
        "workshop_layout": "Montar no layout Steam Workshop: Contents/mods/MOD_ID.", "make_zip": "Também criar um zip.",
        "dry_run": "Apenas mostrar álbuns/faixas detectados; não montar.", "force": "Atualizar mod existente mantendo .ogg já convertidos.",
        "reset": "Apagar totalmente o mod existente, incluindo .ogg.", "help": "Mostrar esta ajuda e sair.",
        "help_lang": "Forçar idioma da ajuda. Códigos: EN, RU, DE, ES, PTBR etc.", "example1": "Build rápido a partir de OGG já convertidos:", "example2": "Mostrar ajuda em português explicitamente:",
    },
}

# Language fallbacks for help. These languages still generate their own True Music translation folders.
HELP_FALLBACKS = {
    "AR": "ES", "CA": "ES", "CH": "EN", "CN": "EN", "CS": "EN", "DA": "EN", "FI": "EN",
    "FR": "EN", "HU": "EN", "ID": "EN", "IT": "EN", "JP": "EN", "KO": "EN", "NL": "EN",
    "NO": "EN", "PH": "EN", "PL": "EN", "PT": "PTBR", "RO": "EN", "TH": "EN", "TR": "EN", "UA": "RU",
}

LOCALE_TO_PZ_LANG = {
    "es_ar": "AR", "ca": "CA", "zh_tw": "CH", "zh_hk": "CH", "zh_mo": "CH", "zh_cn": "CN", "zh_sg": "CN",
    "cs": "CS", "da": "DA", "de": "DE", "es": "ES", "fi": "FI", "fr": "FR", "hu": "HU", "id": "ID",
    "it": "IT", "ja": "JP", "jp": "JP", "ko": "KO", "nl": "NL", "no": "NO", "nb": "NO", "nn": "NO",
    "tl": "PH", "fil": "PH", "pl": "PL", "pt_br": "PTBR", "pt": "PT", "ro": "RO", "ru": "RU",
    "th": "TH", "tr": "TR", "uk": "UA", "ua": "UA",
}

ARG_HELP_KEYS = {
    "--input": "input", "--output": "output", "--mod-id": "mod_id", "--name": "name", "--author": "author",
    "--album-name": "album_name", "--album-mode": "album_mode", "--use-tags": "use_tags", "--manifest-csv": "manifest_csv",
    "--max-tracks-per-album": "max_tracks_per_album", "--modversion": "modversion", "--require-mod": "require_mod",
    "--spawn": "spawn", "--quality": "quality", "--copy-ogg": "copy_ogg", "--rebuild-audio": "rebuild_audio",
    "--skip-audio": "skip_audio", "--languages": "languages", "--workshop-layout": "workshop_layout", "--make-zip": "make_zip",
    "--dry-run": "dry_run", "--force": "force", "--reset": "reset", "--help": "help", "--help-lang": "help_lang",
}

# Compact CLI localization for every language used by PZ True Music.
CLI_TRANSLATIONS = {'AR': {'album_mode': 'Opción del comando.',
        'album_name': 'Opción del comando.',
        'arg_error': 'Error de argumentos: {message}',
        'author': 'Opción del comando.',
        'copy_audio': 'copiar: {src} -> {dst}',
        'copy_ogg': 'Opción del comando.',
        'csv_requires_file': 'Error de argumentos: CSV: file,title,artist,album,genre',
        'description': 'Crea un paquete de música solo con casetes para Project Zomboid Build 42 y PZ True Music.',
        'done': 'Hecho: {path}',
        'dry_run': 'Opción del comando.',
        'dry_run_done': 'Dry-run: el mod no fue construido',
        'enable_mod': 'Activa este mod junto con PZ True Music / truemusic en el juego',
        'example1': 'Opción del comando.',
        'example2': 'Opción del comando.',
        'examples': 'Opciones',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg falló: {error}',
        'ffmpeg_not_found': 'No se encontró ffmpeg. Instala ffmpeg y asegúrate de que esté en PATH.',
        'ffprobe_missing': 'Advertencia: no se encontró ffprobe; no se leerán etiquetas',
        'folder_exists': 'La carpeta ya existe: {path}\nAñade --force para actualizar conservando los .ogg, o --reset para borrar todo.',
        'force': 'Opción del comando.',
        'found_albums': 'Álbumes encontrados: {count}',
        'found_tracks': 'Pistas encontradas: {count}',
        'generic_option': 'Opción del comando.',
        'help': 'Opción del comando.',
        'help_lang': 'Opción del comando.',
        'input': 'Opción del comando.',
        'invalid_album_mode': 'Error de argumentos: --album-mode',
        'invalid_language': 'Error de argumentos: language',
        'lang': 'Opción del comando.',
        'language': 'Idioma',
        'languages': 'Opción del comando.',
        'make_zip': 'Opción del comando.',
        'manifest_csv': 'Opción del comando.',
        'max_tracks_per_album': 'Opción del comando.',
        'missing_required': 'Falta argumento obligatorio: {name}',
        'mod_id': 'Opción del comando.',
        'mod_id_sanitized': 'ID del mod limpiado: {old} -> {new}',
        'modversion': 'Opción del comando.',
        'more_albums': '... más álbumes: {count}',
        'name': 'Opción del comando.',
        'no_audio_files': 'No se encontraron archivos de audio en la carpeta: {path}',
        'no_input_dir': 'La carpeta de música no existe: {path}',
        'optional': 'Opciones',
        'output': 'Opción del comando.',
        'quality': 'Opción del comando.',
        'rebuild_audio': 'Opción del comando.',
        'require_mod': 'Opción del comando.',
        'required': 'Opciones',
        'reset': 'Opción del comando.',
        'skip_audio': 'Opción del comando.',
        'skip_existing': 'omitir existente: {item}',
        'spawn': 'Opción del comando.',
        'supported_folders': 'Carpetas de traducción de True Music compatibles',
        'usage': 'Uso',
        'use_tags': 'Opción del comando.',
        'workshop_layout': 'Opción del comando.',
        'zip_created': 'ZIP: {path}'},
 'CA': {'album_mode': 'Opción del comando.',
        'album_name': 'Opción del comando.',
        'arg_error': 'Error de argumentos: {message}',
        'author': 'Opción del comando.',
        'copy_audio': 'copiar: {src} -> {dst}',
        'copy_ogg': 'Opción del comando.',
        'csv_requires_file': 'Error de argumentos: CSV: file,title,artist,album,genre',
        'description': 'Crea un paquete de música solo con casetes para Project Zomboid Build 42 y PZ True Music.',
        'done': 'Hecho: {path}',
        'dry_run': 'Opción del comando.',
        'dry_run_done': 'Dry-run: el mod no fue construido',
        'enable_mod': 'Activa este mod junto con PZ True Music / truemusic en el juego',
        'example1': 'Opción del comando.',
        'example2': 'Opción del comando.',
        'examples': 'Opciones',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg falló: {error}',
        'ffmpeg_not_found': 'No se encontró ffmpeg. Instala ffmpeg y asegúrate de que esté en PATH.',
        'ffprobe_missing': 'Advertencia: no se encontró ffprobe; no se leerán etiquetas',
        'folder_exists': 'La carpeta ya existe: {path}\nAñade --force para actualizar conservando los .ogg, o --reset para borrar todo.',
        'force': 'Opción del comando.',
        'found_albums': 'Álbumes encontrados: {count}',
        'found_tracks': 'Pistas encontradas: {count}',
        'generic_option': 'Opción del comando.',
        'help': 'Opción del comando.',
        'help_lang': 'Opción del comando.',
        'input': 'Opción del comando.',
        'invalid_album_mode': 'Error de argumentos: --album-mode',
        'invalid_language': 'Error de argumentos: language',
        'lang': 'Opción del comando.',
        'language': 'Idioma',
        'languages': 'Opción del comando.',
        'make_zip': 'Opción del comando.',
        'manifest_csv': 'Opción del comando.',
        'max_tracks_per_album': 'Opción del comando.',
        'missing_required': 'Falta argumento obligatorio: {name}',
        'mod_id': 'Opción del comando.',
        'mod_id_sanitized': 'ID del mod limpiado: {old} -> {new}',
        'modversion': 'Opción del comando.',
        'more_albums': '... más álbumes: {count}',
        'name': 'Opción del comando.',
        'no_audio_files': 'No se encontraron archivos de audio en la carpeta: {path}',
        'no_input_dir': 'La carpeta de música no existe: {path}',
        'optional': 'Opciones',
        'output': 'Opción del comando.',
        'quality': 'Opción del comando.',
        'rebuild_audio': 'Opción del comando.',
        'require_mod': 'Opción del comando.',
        'required': 'Opciones',
        'reset': 'Opción del comando.',
        'skip_audio': 'Opción del comando.',
        'skip_existing': 'omitir existente: {item}',
        'spawn': 'Opción del comando.',
        'supported_folders': 'Carpetas de traducción de True Music compatibles',
        'usage': 'Uso',
        'use_tags': 'Opción del comando.',
        'workshop_layout': 'Opción del comando.',
        'zip_created': 'ZIP: {path}'},
 'CH': {'album_mode': '命令選項。',
        'album_name': '命令選項。',
        'arg_error': '參數錯誤: {message}',
        'author': '命令選項。',
        'copy_audio': '複製: {src} -> {dst}',
        'copy_ogg': '命令選項。',
        'csv_requires_file': '參數錯誤: CSV: file,title,artist,album,genre',
        'description': '為 Project Zomboid Build 42 和 PZ True Music 建立僅含卡帶的音樂包。',
        'done': '完成: {path}',
        'dry_run': '命令選項。',
        'dry_run_done': 'Dry-run：未建立模組',
        'enable_mod': '在遊戲中與 PZ True Music / truemusic 一起啟用此模組',
        'example1': '命令選項。',
        'example2': '命令選項。',
        'examples': '選項',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg 失敗: {error}',
        'ffmpeg_not_found': '找不到 ffmpeg。請安裝 ffmpeg 並確認它在 PATH 中。',
        'ffprobe_missing': '警告：找不到 ffprobe；不會讀取標籤',
        'folder_exists': '資料夾已存在: {path}\n加入 --force 以保留 .ogg 並更新，或加入 --reset 刪除全部。',
        'force': '命令選項。',
        'found_albums': '找到專輯: {count}',
        'found_tracks': '找到曲目: {count}',
        'generic_option': '命令選項。',
        'help': '命令選項。',
        'help_lang': '命令選項。',
        'input': '命令選項。',
        'invalid_album_mode': '參數錯誤: --album-mode',
        'invalid_language': '參數錯誤: language',
        'lang': '命令選項。',
        'language': '語言',
        'languages': '命令選項。',
        'make_zip': '命令選項。',
        'manifest_csv': '命令選項。',
        'max_tracks_per_album': '命令選項。',
        'missing_required': '缺少必要參數: {name}',
        'mod_id': '命令選項。',
        'mod_id_sanitized': '模組 ID 已清理: {old} -> {new}',
        'modversion': '命令選項。',
        'more_albums': '... 更多專輯: {count}',
        'name': '命令選項。',
        'no_audio_files': '資料夾中沒有音訊檔案: {path}',
        'no_input_dir': '音樂資料夾不存在: {path}',
        'optional': '選項',
        'output': '命令選項。',
        'quality': '命令選項。',
        'rebuild_audio': '命令選項。',
        'require_mod': '命令選項。',
        'required': '選項',
        'reset': '命令選項。',
        'skip_audio': '命令選項。',
        'skip_existing': '略過已存在: {item}',
        'spawn': '命令選項。',
        'supported_folders': '支援的 True Music 翻譯資料夾',
        'usage': '用法',
        'use_tags': '命令選項。',
        'workshop_layout': '命令選項。',
        'zip_created': 'ZIP: {path}'},
 'CN': {'album_mode': '命令选项。',
        'album_name': '命令选项。',
        'arg_error': '参数错误: {message}',
        'author': '命令选项。',
        'copy_audio': '复制: {src} -> {dst}',
        'copy_ogg': '命令选项。',
        'csv_requires_file': '参数错误: CSV: file,title,artist,album,genre',
        'description': '为 Project Zomboid Build 42 和 PZ True Music 创建仅含磁带的音乐包。',
        'done': '完成: {path}',
        'dry_run': '命令选项。',
        'dry_run_done': 'Dry-run：未构建模组',
        'enable_mod': '在游戏中与 PZ True Music / truemusic 一起启用此模组',
        'example1': '命令选项。',
        'example2': '命令选项。',
        'examples': '选项',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg 失败: {error}',
        'ffmpeg_not_found': '未找到 ffmpeg。请安装 ffmpeg 并确保它在 PATH 中。',
        'ffprobe_missing': '警告：未找到 ffprobe；不会读取标签',
        'folder_exists': '文件夹已存在: {path}\n添加 --force 以保留 .ogg 并更新，或添加 --reset 删除全部。',
        'force': '命令选项。',
        'found_albums': '找到专辑: {count}',
        'found_tracks': '找到曲目: {count}',
        'generic_option': '命令选项。',
        'help': '命令选项。',
        'help_lang': '命令选项。',
        'input': '命令选项。',
        'invalid_album_mode': '参数错误: --album-mode',
        'invalid_language': '参数错误: language',
        'lang': '命令选项。',
        'language': '语言',
        'languages': '命令选项。',
        'make_zip': '命令选项。',
        'manifest_csv': '命令选项。',
        'max_tracks_per_album': '命令选项。',
        'missing_required': '缺少必需参数: {name}',
        'mod_id': '命令选项。',
        'mod_id_sanitized': '模组 ID 已清理: {old} -> {new}',
        'modversion': '命令选项。',
        'more_albums': '... 更多专辑: {count}',
        'name': '命令选项。',
        'no_audio_files': '文件夹中没有音频文件: {path}',
        'no_input_dir': '音乐文件夹不存在: {path}',
        'optional': '选项',
        'output': '命令选项。',
        'quality': '命令选项。',
        'rebuild_audio': '命令选项。',
        'require_mod': '命令选项。',
        'required': '选项',
        'reset': '命令选项。',
        'skip_audio': '命令选项。',
        'skip_existing': '跳过已存在: {item}',
        'spawn': '命令选项。',
        'supported_folders': '支持的 True Music 翻译文件夹',
        'usage': '用法',
        'use_tags': '命令选项。',
        'workshop_layout': '命令选项。',
        'zip_created': 'ZIP: {path}'},
 'CS': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'DA': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'DE': {'album_mode': 'Befehlsoption.',
        'album_name': 'Befehlsoption.',
        'arg_error': 'Argumentfehler: {message}',
        'author': 'Befehlsoption.',
        'copy_audio': 'kopieren: {src} -> {dst}',
        'copy_ogg': 'Befehlsoption.',
        'csv_requires_file': 'Argumentfehler: CSV: file,title,artist,album,genre',
        'description': 'Erstellt ein Kassetten-Musikpaket für Project Zomboid Build 42 und PZ True Music.',
        'done': 'Fertig: {path}',
        'dry_run': 'Befehlsoption.',
        'dry_run_done': 'Dry-run: Mod wurde nicht gebaut',
        'enable_mod': 'Aktiviere diesen Mod im Spiel zusammen mit PZ True Music / truemusic',
        'example1': 'Befehlsoption.',
        'example2': 'Befehlsoption.',
        'examples': 'Optionen',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg fehlgeschlagen: {error}',
        'ffmpeg_not_found': 'ffmpeg wurde nicht gefunden. Installiere ffmpeg und stelle sicher, dass es in PATH liegt.',
        'ffprobe_missing': 'Warnung: ffprobe wurde nicht gefunden; Tags werden nicht gelesen',
        'folder_exists': 'Ordner existiert bereits: {path}\nFüge --force hinzu, um zu aktualisieren und .ogg zu behalten, oder --reset, um alles zu löschen.',
        'force': 'Befehlsoption.',
        'found_albums': 'Gefundene Alben: {count}',
        'found_tracks': 'Gefundene Titel: {count}',
        'generic_option': 'Befehlsoption.',
        'help': 'Befehlsoption.',
        'help_lang': 'Befehlsoption.',
        'input': 'Befehlsoption.',
        'invalid_album_mode': 'Argumentfehler: --album-mode',
        'invalid_language': 'Argumentfehler: language',
        'lang': 'Befehlsoption.',
        'language': 'Sprache',
        'languages': 'Befehlsoption.',
        'make_zip': 'Befehlsoption.',
        'manifest_csv': 'Befehlsoption.',
        'max_tracks_per_album': 'Befehlsoption.',
        'missing_required': 'Pflichtargument fehlt: {name}',
        'mod_id': 'Befehlsoption.',
        'mod_id_sanitized': 'Mod-ID bereinigt: {old} -> {new}',
        'modversion': 'Befehlsoption.',
        'more_albums': '... weitere Alben: {count}',
        'name': 'Befehlsoption.',
        'no_audio_files': 'Keine Audiodateien im Ordner gefunden: {path}',
        'no_input_dir': 'Musikordner existiert nicht: {path}',
        'optional': 'Optionen',
        'output': 'Befehlsoption.',
        'quality': 'Befehlsoption.',
        'rebuild_audio': 'Befehlsoption.',
        'require_mod': 'Befehlsoption.',
        'required': 'Optionen',
        'reset': 'Befehlsoption.',
        'skip_audio': 'Befehlsoption.',
        'skip_existing': 'vorhanden überspringen: {item}',
        'spawn': 'Befehlsoption.',
        'supported_folders': 'Unterstützte True-Music-Übersetzungsordner',
        'usage': 'Verwendung',
        'use_tags': 'Befehlsoption.',
        'workshop_layout': 'Befehlsoption.',
        'zip_created': 'ZIP: {path}'},
 'EN': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'ES': {'album_mode': 'Opción del comando.',
        'album_name': 'Opción del comando.',
        'arg_error': 'Error de argumentos: {message}',
        'author': 'Opción del comando.',
        'copy_audio': 'copiar: {src} -> {dst}',
        'copy_ogg': 'Opción del comando.',
        'csv_requires_file': 'Error de argumentos: CSV: file,title,artist,album,genre',
        'description': 'Crea un paquete de música solo con casetes para Project Zomboid Build 42 y PZ True Music.',
        'done': 'Hecho: {path}',
        'dry_run': 'Opción del comando.',
        'dry_run_done': 'Dry-run: el mod no fue construido',
        'enable_mod': 'Activa este mod junto con PZ True Music / truemusic en el juego',
        'example1': 'Opción del comando.',
        'example2': 'Opción del comando.',
        'examples': 'Opciones',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg falló: {error}',
        'ffmpeg_not_found': 'No se encontró ffmpeg. Instala ffmpeg y asegúrate de que esté en PATH.',
        'ffprobe_missing': 'Advertencia: no se encontró ffprobe; no se leerán etiquetas',
        'folder_exists': 'La carpeta ya existe: {path}\nAñade --force para actualizar conservando los .ogg, o --reset para borrar todo.',
        'force': 'Opción del comando.',
        'found_albums': 'Álbumes encontrados: {count}',
        'found_tracks': 'Pistas encontradas: {count}',
        'generic_option': 'Opción del comando.',
        'help': 'Opción del comando.',
        'help_lang': 'Opción del comando.',
        'input': 'Opción del comando.',
        'invalid_album_mode': 'Error de argumentos: --album-mode',
        'invalid_language': 'Error de argumentos: language',
        'lang': 'Opción del comando.',
        'language': 'Idioma',
        'languages': 'Opción del comando.',
        'make_zip': 'Opción del comando.',
        'manifest_csv': 'Opción del comando.',
        'max_tracks_per_album': 'Opción del comando.',
        'missing_required': 'Falta argumento obligatorio: {name}',
        'mod_id': 'Opción del comando.',
        'mod_id_sanitized': 'ID del mod limpiado: {old} -> {new}',
        'modversion': 'Opción del comando.',
        'more_albums': '... más álbumes: {count}',
        'name': 'Opción del comando.',
        'no_audio_files': 'No se encontraron archivos de audio en la carpeta: {path}',
        'no_input_dir': 'La carpeta de música no existe: {path}',
        'optional': 'Opciones',
        'output': 'Opción del comando.',
        'quality': 'Opción del comando.',
        'rebuild_audio': 'Opción del comando.',
        'require_mod': 'Opción del comando.',
        'required': 'Opciones',
        'reset': 'Opción del comando.',
        'skip_audio': 'Opción del comando.',
        'skip_existing': 'omitir existente: {item}',
        'spawn': 'Opción del comando.',
        'supported_folders': 'Carpetas de traducción de True Music compatibles',
        'usage': 'Uso',
        'use_tags': 'Opción del comando.',
        'workshop_layout': 'Opción del comando.',
        'zip_created': 'ZIP: {path}'},
 'FI': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'FR': {'album_mode': 'Option de commande.',
        'album_name': 'Option de commande.',
        'arg_error': 'Erreur d’arguments : {message}',
        'author': 'Option de commande.',
        'copy_audio': 'copie : {src} -> {dst}',
        'copy_ogg': 'Option de commande.',
        'csv_requires_file': 'Erreur d’arguments : CSV: file,title,artist,album,genre',
        'description': 'Crée un pack musical uniquement avec des cassettes pour Project Zomboid Build 42 et PZ True Music.',
        'done': 'Terminé : {path}',
        'dry_run': 'Option de commande.',
        'dry_run_done': 'Dry-run : le mod n’a pas été construit',
        'enable_mod': 'Active ce mod avec PZ True Music / truemusic dans le jeu',
        'example1': 'Option de commande.',
        'example2': 'Option de commande.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg : {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg a échoué : {error}',
        'ffmpeg_not_found': 'ffmpeg est introuvable. Installe ffmpeg et vérifie qu’il est dans PATH.',
        'ffprobe_missing': 'Avertissement : ffprobe introuvable ; les tags ne seront pas lus',
        'folder_exists': 'Le dossier existe déjà : {path}\nAjoute --force pour mettre à jour en gardant les .ogg, ou --reset pour tout supprimer.',
        'force': 'Option de commande.',
        'found_albums': 'Albums trouvés : {count}',
        'found_tracks': 'Pistes trouvées : {count}',
        'generic_option': 'Option de commande.',
        'help': 'Option de commande.',
        'help_lang': 'Option de commande.',
        'input': 'Option de commande.',
        'invalid_album_mode': 'Erreur d’arguments : --album-mode',
        'invalid_language': 'Erreur d’arguments : language',
        'lang': 'Option de commande.',
        'language': 'Langue',
        'languages': 'Option de commande.',
        'make_zip': 'Option de commande.',
        'manifest_csv': 'Option de commande.',
        'max_tracks_per_album': 'Option de commande.',
        'missing_required': 'Argument obligatoire manquant : {name}',
        'mod_id': 'Option de commande.',
        'mod_id_sanitized': 'ID du mod nettoyé : {old} -> {new}',
        'modversion': 'Option de commande.',
        'more_albums': '... albums supplémentaires : {count}',
        'name': 'Option de commande.',
        'no_audio_files': 'Aucun fichier audio trouvé dans le dossier : {path}',
        'no_input_dir': 'Le dossier de musique n’existe pas : {path}',
        'optional': 'Options',
        'output': 'Option de commande.',
        'quality': 'Option de commande.',
        'rebuild_audio': 'Option de commande.',
        'require_mod': 'Option de commande.',
        'required': 'Options',
        'reset': 'Option de commande.',
        'skip_audio': 'Option de commande.',
        'skip_existing': 'ignorer existant : {item}',
        'spawn': 'Option de commande.',
        'supported_folders': 'Dossiers de traduction True Music pris en charge',
        'usage': 'Utilisation',
        'use_tags': 'Option de commande.',
        'workshop_layout': 'Option de commande.',
        'zip_created': 'ZIP: {path}'},
 'HU': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'ID': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'IT': {'album_mode': 'Opzione comando.',
        'album_name': 'Opzione comando.',
        'arg_error': 'Errore argomenti: {message}',
        'author': 'Opzione comando.',
        'copy_audio': 'copia: {src} -> {dst}',
        'copy_ogg': 'Opzione comando.',
        'csv_requires_file': 'Errore argomenti: CSV: file,title,artist,album,genre',
        'description': 'Crea un pacchetto musicale solo cassette per Project Zomboid Build 42 e PZ True Music.',
        'done': 'Fatto: {path}',
        'dry_run': 'Opzione comando.',
        'dry_run_done': 'Dry-run: mod non creato',
        'enable_mod': 'Attiva questo mod insieme a PZ True Music / truemusic nel gioco',
        'example1': 'Opzione comando.',
        'example2': 'Opzione comando.',
        'examples': 'Opzioni',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg non riuscito: {error}',
        'ffmpeg_not_found': 'ffmpeg non trovato. Installa ffmpeg e assicurati che sia nel PATH.',
        'ffprobe_missing': 'Avviso: ffprobe non trovato; i tag non saranno letti',
        'folder_exists': 'La cartella esiste già: {path}\nAggiungi --force per aggiornare mantenendo gli .ogg, o --reset per eliminare tutto.',
        'force': 'Opzione comando.',
        'found_albums': 'Album trovati: {count}',
        'found_tracks': 'Tracce trovate: {count}',
        'generic_option': 'Opzione comando.',
        'help': 'Opzione comando.',
        'help_lang': 'Opzione comando.',
        'input': 'Opzione comando.',
        'invalid_album_mode': 'Errore argomenti: --album-mode',
        'invalid_language': 'Errore argomenti: language',
        'lang': 'Opzione comando.',
        'language': 'Lingua',
        'languages': 'Opzione comando.',
        'make_zip': 'Opzione comando.',
        'manifest_csv': 'Opzione comando.',
        'max_tracks_per_album': 'Opzione comando.',
        'missing_required': 'Argomento obbligatorio mancante: {name}',
        'mod_id': 'Opzione comando.',
        'mod_id_sanitized': 'ID mod pulito: {old} -> {new}',
        'modversion': 'Opzione comando.',
        'more_albums': '... altri album: {count}',
        'name': 'Opzione comando.',
        'no_audio_files': 'Nessun file audio trovato nella cartella: {path}',
        'no_input_dir': 'La cartella musica non esiste: {path}',
        'optional': 'Opzioni',
        'output': 'Opzione comando.',
        'quality': 'Opzione comando.',
        'rebuild_audio': 'Opzione comando.',
        'require_mod': 'Opzione comando.',
        'required': 'Opzioni',
        'reset': 'Opzione comando.',
        'skip_audio': 'Opzione comando.',
        'skip_existing': 'salta esistente: {item}',
        'spawn': 'Opzione comando.',
        'supported_folders': 'Cartelle di traduzione True Music supportate',
        'usage': 'Uso',
        'use_tags': 'Opzione comando.',
        'workshop_layout': 'Opzione comando.',
        'zip_created': 'ZIP: {path}'},
 'JP': {'album_mode': 'コマンドオプション。',
        'album_name': 'コマンドオプション。',
        'arg_error': '引数エラー: {message}',
        'author': 'コマンドオプション。',
        'copy_audio': 'コピー: {src} -> {dst}',
        'copy_ogg': 'コマンドオプション。',
        'csv_requires_file': '引数エラー: CSV: file,title,artist,album,genre',
        'description': 'Project Zomboid Build 42 と PZ True Music 用のカセット専用音楽パックを作成します。',
        'done': '完了: {path}',
        'dry_run': 'コマンドオプション。',
        'dry_run_done': 'Dry-run: MODは作成されませんでした',
        'enable_mod': 'ゲーム内でこのMODを PZ True Music / truemusic と一緒に有効にしてください',
        'example1': 'コマンドオプション。',
        'example2': 'コマンドオプション。',
        'examples': 'オプション',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg 失敗: {error}',
        'ffmpeg_not_found': 'ffmpeg が見つかりません。ffmpeg をインストールし、PATH に追加してください。',
        'ffprobe_missing': '警告: ffprobe が見つからないため、タグは読み取られません',
        'folder_exists': 'フォルダーは既に存在します: {path}\n既存の .ogg を保持して更新するには --force、すべて削除するには --reset を追加してください。',
        'force': 'コマンドオプション。',
        'found_albums': '見つかったアルバム: {count}',
        'found_tracks': '見つかったトラック: {count}',
        'generic_option': 'コマンドオプション。',
        'help': 'コマンドオプション。',
        'help_lang': 'コマンドオプション。',
        'input': 'コマンドオプション。',
        'invalid_album_mode': '引数エラー: --album-mode',
        'invalid_language': '引数エラー: language',
        'lang': 'コマンドオプション。',
        'language': '言語',
        'languages': 'コマンドオプション。',
        'make_zip': 'コマンドオプション。',
        'manifest_csv': 'コマンドオプション。',
        'max_tracks_per_album': 'コマンドオプション。',
        'missing_required': '必須引数がありません: {name}',
        'mod_id': 'コマンドオプション。',
        'mod_id_sanitized': 'MOD ID を整理しました: {old} -> {new}',
        'modversion': 'コマンドオプション。',
        'more_albums': '... 追加アルバム: {count}',
        'name': 'コマンドオプション。',
        'no_audio_files': 'フォルダー内に音声ファイルがありません: {path}',
        'no_input_dir': '音楽フォルダーが存在しません: {path}',
        'optional': 'オプション',
        'output': 'コマンドオプション。',
        'quality': 'コマンドオプション。',
        'rebuild_audio': 'コマンドオプション。',
        'require_mod': 'コマンドオプション。',
        'required': 'オプション',
        'reset': 'コマンドオプション。',
        'skip_audio': 'コマンドオプション。',
        'skip_existing': '既存をスキップ: {item}',
        'spawn': 'コマンドオプション。',
        'supported_folders': '対応する True Music 翻訳フォルダー',
        'usage': '使い方',
        'use_tags': 'コマンドオプション。',
        'workshop_layout': 'コマンドオプション。',
        'zip_created': 'ZIP: {path}'},
 'KO': {'album_mode': '명령 옵션.',
        'album_name': '명령 옵션.',
        'arg_error': '인수 오류: {message}',
        'author': '명령 옵션.',
        'copy_audio': '복사: {src} -> {dst}',
        'copy_ogg': '명령 옵션.',
        'csv_requires_file': '인수 오류: CSV: file,title,artist,album,genre',
        'description': 'Project Zomboid Build 42 및 PZ True Music용 카세트 전용 음악 팩을 만듭니다.',
        'done': '완료: {path}',
        'dry_run': '명령 옵션.',
        'dry_run_done': 'Dry-run: 모드를 만들지 않았습니다',
        'enable_mod': '게임에서 이 모드를 PZ True Music / truemusic과 함께 활성화하세요',
        'example1': '명령 옵션.',
        'example2': '명령 옵션.',
        'examples': '옵션',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg 실패: {error}',
        'ffmpeg_not_found': 'ffmpeg를 찾을 수 없습니다. ffmpeg를 설치하고 PATH에 있는지 확인하세요.',
        'ffprobe_missing': '경고: ffprobe를 찾을 수 없어 태그를 읽지 않습니다',
        'folder_exists': '폴더가 이미 있습니다: {path}\n변환된 .ogg를 유지하며 업데이트하려면 --force, 모두 삭제하려면 --reset을 추가하세요.',
        'force': '명령 옵션.',
        'found_albums': '찾은 앨범: {count}',
        'found_tracks': '찾은 트랙: {count}',
        'generic_option': '명령 옵션.',
        'help': '명령 옵션.',
        'help_lang': '명령 옵션.',
        'input': '명령 옵션.',
        'invalid_album_mode': '인수 오류: --album-mode',
        'invalid_language': '인수 오류: language',
        'lang': '명령 옵션.',
        'language': '언어',
        'languages': '명령 옵션.',
        'make_zip': '명령 옵션.',
        'manifest_csv': '명령 옵션.',
        'max_tracks_per_album': '명령 옵션.',
        'missing_required': '필수 인수가 없습니다: {name}',
        'mod_id': '명령 옵션.',
        'mod_id_sanitized': '모드 ID 정리됨: {old} -> {new}',
        'modversion': '명령 옵션.',
        'more_albums': '... 추가 앨범: {count}',
        'name': '명령 옵션.',
        'no_audio_files': '폴더에 오디오 파일이 없습니다: {path}',
        'no_input_dir': '음악 폴더가 없습니다: {path}',
        'optional': '옵션',
        'output': '명령 옵션.',
        'quality': '명령 옵션.',
        'rebuild_audio': '명령 옵션.',
        'require_mod': '명령 옵션.',
        'required': '옵션',
        'reset': '명령 옵션.',
        'skip_audio': '명령 옵션.',
        'skip_existing': '기존 파일 건너뜀: {item}',
        'spawn': '명령 옵션.',
        'supported_folders': '지원되는 True Music 번역 폴더',
        'usage': '사용법',
        'use_tags': '명령 옵션.',
        'workshop_layout': '명령 옵션.',
        'zip_created': 'ZIP: {path}'},
 'NL': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'NO': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'PH': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'PL': {'album_mode': 'Opcja polecenia.',
        'album_name': 'Opcja polecenia.',
        'arg_error': 'Błąd argumentów: {message}',
        'author': 'Opcja polecenia.',
        'copy_audio': 'kopiuj: {src} -> {dst}',
        'copy_ogg': 'Opcja polecenia.',
        'csv_requires_file': 'Błąd argumentów: CSV: file,title,artist,album,genre',
        'description': 'Tworzy pakiet muzyczny tylko z kasetami dla Project Zomboid Build 42 i PZ True Music.',
        'done': 'Gotowe: {path}',
        'dry_run': 'Opcja polecenia.',
        'dry_run_done': 'Dry-run: mod nie został zbudowany',
        'enable_mod': 'W grze włącz ten mod razem z PZ True Music / truemusic',
        'example1': 'Opcja polecenia.',
        'example2': 'Opcja polecenia.',
        'examples': 'Opcje',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg nie powiódł się: {error}',
        'ffmpeg_not_found': 'Nie znaleziono ffmpeg. Zainstaluj ffmpeg i upewnij się, że jest w PATH.',
        'ffprobe_missing': 'Ostrzeżenie: nie znaleziono ffprobe; tagi nie zostaną odczytane',
        'folder_exists': 'Folder już istnieje: {path}\nDodaj --force, aby zaktualizować i zachować .ogg, albo --reset, aby usunąć wszystko.',
        'force': 'Opcja polecenia.',
        'found_albums': 'Znalezione albumy: {count}',
        'found_tracks': 'Znalezione utwory: {count}',
        'generic_option': 'Opcja polecenia.',
        'help': 'Opcja polecenia.',
        'help_lang': 'Opcja polecenia.',
        'input': 'Opcja polecenia.',
        'invalid_album_mode': 'Błąd argumentów: --album-mode',
        'invalid_language': 'Błąd argumentów: language',
        'lang': 'Opcja polecenia.',
        'language': 'Język',
        'languages': 'Opcja polecenia.',
        'make_zip': 'Opcja polecenia.',
        'manifest_csv': 'Opcja polecenia.',
        'max_tracks_per_album': 'Opcja polecenia.',
        'missing_required': 'Brak wymaganego argumentu: {name}',
        'mod_id': 'Opcja polecenia.',
        'mod_id_sanitized': 'ID moda oczyszczone: {old} -> {new}',
        'modversion': 'Opcja polecenia.',
        'more_albums': '... więcej albumów: {count}',
        'name': 'Opcja polecenia.',
        'no_audio_files': 'Nie znaleziono plików audio w folderze: {path}',
        'no_input_dir': 'Folder z muzyką nie istnieje: {path}',
        'optional': 'Opcje',
        'output': 'Opcja polecenia.',
        'quality': 'Opcja polecenia.',
        'rebuild_audio': 'Opcja polecenia.',
        'require_mod': 'Opcja polecenia.',
        'required': 'Opcje',
        'reset': 'Opcja polecenia.',
        'skip_audio': 'Opcja polecenia.',
        'skip_existing': 'pomiń istniejący: {item}',
        'spawn': 'Opcja polecenia.',
        'supported_folders': 'Obsługiwane foldery tłumaczeń True Music',
        'usage': 'Użycie',
        'use_tags': 'Opcja polecenia.',
        'workshop_layout': 'Opcja polecenia.',
        'zip_created': 'ZIP: {path}'},
 'PT': {'album_mode': 'Opção de comando.',
        'album_name': 'Opção de comando.',
        'arg_error': 'Erro de argumentos: {message}',
        'author': 'Opção de comando.',
        'copy_audio': 'copiar: {src} -> {dst}',
        'copy_ogg': 'Opção de comando.',
        'csv_requires_file': 'Erro de argumentos: CSV: file,title,artist,album,genre',
        'description': 'Cria um pacote de música somente com fitas cassete para Project Zomboid Build 42 e PZ True Music.',
        'done': 'Pronto: {path}',
        'dry_run': 'Opção de comando.',
        'dry_run_done': 'Dry-run: o mod não foi construído',
        'enable_mod': 'Ative este mod junto com PZ True Music / truemusic no jogo',
        'example1': 'Opção de comando.',
        'example2': 'Opção de comando.',
        'examples': 'Opções',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg falhou: {error}',
        'ffmpeg_not_found': 'ffmpeg não foi encontrado. Instale o ffmpeg e verifique se ele está no PATH.',
        'ffprobe_missing': 'Aviso: ffprobe não foi encontrado; tags não serão lidas',
        'folder_exists': 'A pasta já existe: {path}\nAdicione --force para atualizar mantendo os .ogg, ou --reset para apagar tudo.',
        'force': 'Opção de comando.',
        'found_albums': 'Álbuns encontrados: {count}',
        'found_tracks': 'Faixas encontradas: {count}',
        'generic_option': 'Opção de comando.',
        'help': 'Opção de comando.',
        'help_lang': 'Opção de comando.',
        'input': 'Opção de comando.',
        'invalid_album_mode': 'Erro de argumentos: --album-mode',
        'invalid_language': 'Erro de argumentos: language',
        'lang': 'Opção de comando.',
        'language': 'Idioma',
        'languages': 'Opção de comando.',
        'make_zip': 'Opção de comando.',
        'manifest_csv': 'Opção de comando.',
        'max_tracks_per_album': 'Opção de comando.',
        'missing_required': 'Argumento obrigatório ausente: {name}',
        'mod_id': 'Opção de comando.',
        'mod_id_sanitized': 'ID do mod limpo: {old} -> {new}',
        'modversion': 'Opção de comando.',
        'more_albums': '... mais álbuns: {count}',
        'name': 'Opção de comando.',
        'no_audio_files': 'Nenhum arquivo de áudio encontrado na pasta: {path}',
        'no_input_dir': 'A pasta de música não existe: {path}',
        'optional': 'Opções',
        'output': 'Opção de comando.',
        'quality': 'Opção de comando.',
        'rebuild_audio': 'Opção de comando.',
        'require_mod': 'Opção de comando.',
        'required': 'Opções',
        'reset': 'Opção de comando.',
        'skip_audio': 'Opção de comando.',
        'skip_existing': 'pular existente: {item}',
        'spawn': 'Opção de comando.',
        'supported_folders': 'Pastas de tradução True Music compatíveis',
        'usage': 'Uso',
        'use_tags': 'Opção de comando.',
        'workshop_layout': 'Opção de comando.',
        'zip_created': 'ZIP: {path}'},
 'PTBR': {'album_mode': 'Opção de comando.',
          'album_name': 'Opção de comando.',
          'arg_error': 'Erro de argumentos: {message}',
          'author': 'Opção de comando.',
          'copy_audio': 'copiar: {src} -> {dst}',
          'copy_ogg': 'Opção de comando.',
          'csv_requires_file': 'Erro de argumentos: CSV: file,title,artist,album,genre',
          'description': 'Cria um pacote de música somente com fitas cassete para Project Zomboid Build 42 e PZ True Music.',
          'done': 'Pronto: {path}',
          'dry_run': 'Opção de comando.',
          'dry_run_done': 'Dry-run: o mod não foi construído',
          'enable_mod': 'Ative este mod junto com PZ True Music / truemusic no jogo',
          'example1': 'Opção de comando.',
          'example2': 'Opção de comando.',
          'examples': 'Opções',
          'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
          'ffmpeg_failed': 'ffmpeg falhou: {error}',
          'ffmpeg_not_found': 'ffmpeg não foi encontrado. Instale o ffmpeg e verifique se ele está no PATH.',
          'ffprobe_missing': 'Aviso: ffprobe não foi encontrado; tags não serão lidas',
          'folder_exists': 'A pasta já existe: {path}\nAdicione --force para atualizar mantendo os .ogg, ou --reset para apagar tudo.',
          'force': 'Opção de comando.',
          'found_albums': 'Álbuns encontrados: {count}',
          'found_tracks': 'Faixas encontradas: {count}',
          'generic_option': 'Opção de comando.',
          'help': 'Opção de comando.',
          'help_lang': 'Opção de comando.',
          'input': 'Opção de comando.',
          'invalid_album_mode': 'Erro de argumentos: --album-mode',
          'invalid_language': 'Erro de argumentos: language',
          'lang': 'Opção de comando.',
          'language': 'Idioma',
          'languages': 'Opção de comando.',
          'make_zip': 'Opção de comando.',
          'manifest_csv': 'Opção de comando.',
          'max_tracks_per_album': 'Opção de comando.',
          'missing_required': 'Argumento obrigatório ausente: {name}',
          'mod_id': 'Opção de comando.',
          'mod_id_sanitized': 'ID do mod limpo: {old} -> {new}',
          'modversion': 'Opção de comando.',
          'more_albums': '... mais álbuns: {count}',
          'name': 'Opção de comando.',
          'no_audio_files': 'Nenhum arquivo de áudio encontrado na pasta: {path}',
          'no_input_dir': 'A pasta de música não existe: {path}',
          'optional': 'Opções',
          'output': 'Opção de comando.',
          'quality': 'Opção de comando.',
          'rebuild_audio': 'Opção de comando.',
          'require_mod': 'Opção de comando.',
          'required': 'Opções',
          'reset': 'Opção de comando.',
          'skip_audio': 'Opção de comando.',
          'skip_existing': 'pular existente: {item}',
          'spawn': 'Opção de comando.',
          'supported_folders': 'Pastas de tradução True Music compatíveis',
          'usage': 'Uso',
          'use_tags': 'Opção de comando.',
          'workshop_layout': 'Opção de comando.',
          'zip_created': 'ZIP: {path}'},
 'RO': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'RU': {'album_mode': 'Параметр команды.',
        'album_name': 'Параметр команды.',
        'arg_error': 'Ошибка параметров: {message}',
        'author': 'Параметр команды.',
        'copy_audio': 'копирование: {src} -> {dst}',
        'copy_ogg': 'Параметр команды.',
        'csv_requires_file': 'Ошибка параметров: CSV: file,title,artist,album,genre',
        'description': 'Собирает music-pack только с кассетами для Project Zomboid Build 42 и PZ True Music.',
        'done': 'Готово: {path}',
        'dry_run': 'Параметр команды.',
        'dry_run_done': 'Dry-run: мод не собирался',
        'enable_mod': 'В игре включи этот мод вместе с PZ True Music / truemusic',
        'example1': 'Параметр команды.',
        'example2': 'Параметр команды.',
        'examples': 'Параметры',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg завершился с ошибкой: {error}',
        'ffmpeg_not_found': 'ffmpeg не найден. Установи ffmpeg и убедись, что он доступен в PATH.',
        'ffprobe_missing': 'Предупреждение: ffprobe не найден, теги прочитаны не будут',
        'folder_exists': 'Папка уже существует: {path}\n'
                         'Добавь --force, чтобы обновить мод, сохранив уже сконвертированные .ogg, или --reset, чтобы удалить всё.',
        'force': 'Параметр команды.',
        'found_albums': 'Найдено альбомов: {count}',
        'found_tracks': 'Найдено треков: {count}',
        'generic_option': 'Параметр команды.',
        'help': 'Параметр команды.',
        'help_lang': 'Параметр команды.',
        'input': 'Параметр команды.',
        'invalid_album_mode': 'Ошибка параметров: --album-mode',
        'invalid_language': 'Ошибка параметров: language',
        'lang': 'Параметр команды.',
        'language': 'Язык',
        'languages': 'Параметр команды.',
        'make_zip': 'Параметр команды.',
        'manifest_csv': 'Параметр команды.',
        'max_tracks_per_album': 'Параметр команды.',
        'missing_required': 'Не указан обязательный параметр: {name}',
        'mod_id': 'Параметр команды.',
        'mod_id_sanitized': 'ID мода очищен: {old} -> {new}',
        'modversion': 'Параметр команды.',
        'more_albums': '... ещё альбомов: {count}',
        'name': 'Параметр команды.',
        'no_audio_files': 'В папке нет аудиофайлов: {path}',
        'no_input_dir': 'Папка с музыкой не существует: {path}',
        'optional': 'Параметры',
        'output': 'Параметр команды.',
        'quality': 'Параметр команды.',
        'rebuild_audio': 'Параметр команды.',
        'require_mod': 'Параметр команды.',
        'required': 'Параметры',
        'reset': 'Параметр команды.',
        'skip_audio': 'Параметр команды.',
        'skip_existing': 'пропуск существующего файла: {item}',
        'spawn': 'Параметр команды.',
        'supported_folders': 'Поддерживаемые папки переводов True Music',
        'usage': 'Использование',
        'use_tags': 'Параметр команды.',
        'workshop_layout': 'Параметр команды.',
        'zip_created': 'ZIP: {path}'},
 'TH': {'album_mode': 'Command option.',
        'album_name': 'Command option.',
        'arg_error': 'Argument error: {message}',
        'author': 'Command option.',
        'copy_audio': 'copy: {src} -> {dst}',
        'copy_ogg': 'Command option.',
        'csv_requires_file': 'Argument error: CSV: file,title,artist,album,genre',
        'description': 'Build a cassette-only Project Zomboid Build 42 music pack for PZ True Music.',
        'done': 'Done: {path}',
        'dry_run': 'Command option.',
        'dry_run_done': 'Dry-run: mod was not built',
        'enable_mod': 'Enable this mod together with PZ True Music / truemusic in the game',
        'example1': 'Command option.',
        'example2': 'Command option.',
        'examples': 'Options',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg failed: {error}',
        'ffmpeg_not_found': 'ffmpeg was not found. Install ffmpeg and make sure it is available in PATH.',
        'ffprobe_missing': 'Warning: ffprobe was not found; tags will not be read',
        'folder_exists': 'Folder already exists: {path}\nAdd --force to update the mod while keeping converted .ogg files, or --reset to delete everything.',
        'force': 'Command option.',
        'found_albums': 'Albums found: {count}',
        'found_tracks': 'Tracks found: {count}',
        'generic_option': 'Command option.',
        'help': 'Command option.',
        'help_lang': 'Command option.',
        'input': 'Command option.',
        'invalid_album_mode': 'Argument error: --album-mode',
        'invalid_language': 'Argument error: language',
        'lang': 'Command option.',
        'language': 'Language',
        'languages': 'Command option.',
        'make_zip': 'Command option.',
        'manifest_csv': 'Command option.',
        'max_tracks_per_album': 'Command option.',
        'missing_required': 'Missing required argument: {name}',
        'mod_id': 'Command option.',
        'mod_id_sanitized': 'Mod ID sanitized: {old} -> {new}',
        'modversion': 'Command option.',
        'more_albums': '... more albums: {count}',
        'name': 'Command option.',
        'no_audio_files': 'No audio files found in folder: {path}',
        'no_input_dir': 'Music folder does not exist: {path}',
        'optional': 'Options',
        'output': 'Command option.',
        'quality': 'Command option.',
        'rebuild_audio': 'Command option.',
        'require_mod': 'Command option.',
        'required': 'Options',
        'reset': 'Command option.',
        'skip_audio': 'Command option.',
        'skip_existing': 'skip existing: {item}',
        'spawn': 'Command option.',
        'supported_folders': 'Supported True Music translation folders',
        'usage': 'Usage',
        'use_tags': 'Command option.',
        'workshop_layout': 'Command option.',
        'zip_created': 'ZIP: {path}'},
 'TR': {'album_mode': 'Komut seçeneği.',
        'album_name': 'Komut seçeneği.',
        'arg_error': 'Argüman hatası: {message}',
        'author': 'Komut seçeneği.',
        'copy_audio': 'kopyala: {src} -> {dst}',
        'copy_ogg': 'Komut seçeneği.',
        'csv_requires_file': 'Argüman hatası: CSV: file,title,artist,album,genre',
        'description': 'Project Zomboid Build 42 ve PZ True Music için yalnızca kaset içeren müzik paketi oluşturur.',
        'done': 'Tamamlandı: {path}',
        'dry_run': 'Komut seçeneği.',
        'dry_run_done': 'Dry-run: mod oluşturulmadı',
        'enable_mod': 'Oyunda bu modu PZ True Music / truemusic ile birlikte etkinleştir',
        'example1': 'Komut seçeneği.',
        'example2': 'Komut seçeneği.',
        'examples': 'Seçenekler',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg başarısız: {error}',
        'ffmpeg_not_found': 'ffmpeg bulunamadı. ffmpeg kur ve PATH içinde olduğundan emin ol.',
        'ffprobe_missing': 'Uyarı: ffprobe bulunamadı; etiketler okunmayacak',
        'folder_exists': 'Klasör zaten var: {path}\n.ogg dosyalarını koruyarak güncellemek için --force, her şeyi silmek için --reset ekle.',
        'force': 'Komut seçeneği.',
        'found_albums': 'Bulunan albümler: {count}',
        'found_tracks': 'Bulunan parçalar: {count}',
        'generic_option': 'Komut seçeneği.',
        'help': 'Komut seçeneği.',
        'help_lang': 'Komut seçeneği.',
        'input': 'Komut seçeneği.',
        'invalid_album_mode': 'Argüman hatası: --album-mode',
        'invalid_language': 'Argüman hatası: language',
        'lang': 'Komut seçeneği.',
        'language': 'Dil',
        'languages': 'Komut seçeneği.',
        'make_zip': 'Komut seçeneği.',
        'manifest_csv': 'Komut seçeneği.',
        'max_tracks_per_album': 'Komut seçeneği.',
        'missing_required': 'Zorunlu argüman eksik: {name}',
        'mod_id': 'Komut seçeneği.',
        'mod_id_sanitized': 'Mod ID temizlendi: {old} -> {new}',
        'modversion': 'Komut seçeneği.',
        'more_albums': '... ek albüm: {count}',
        'name': 'Komut seçeneği.',
        'no_audio_files': 'Klasörde ses dosyası bulunamadı: {path}',
        'no_input_dir': 'Müzik klasörü yok: {path}',
        'optional': 'Seçenekler',
        'output': 'Komut seçeneği.',
        'quality': 'Komut seçeneği.',
        'rebuild_audio': 'Komut seçeneği.',
        'require_mod': 'Komut seçeneği.',
        'required': 'Seçenekler',
        'reset': 'Komut seçeneği.',
        'skip_audio': 'Komut seçeneği.',
        'skip_existing': 'var olanı atla: {item}',
        'spawn': 'Komut seçeneği.',
        'supported_folders': 'Desteklenen True Music çeviri klasörleri',
        'usage': 'Kullanım',
        'use_tags': 'Komut seçeneği.',
        'workshop_layout': 'Komut seçeneği.',
        'zip_created': 'ZIP: {path}'},
 'UA': {'album_mode': 'Параметр команди.',
        'album_name': 'Параметр команди.',
        'arg_error': 'Помилка параметрів: {message}',
        'author': 'Параметр команди.',
        'copy_audio': 'копіювання: {src} -> {dst}',
        'copy_ogg': 'Параметр команди.',
        'csv_requires_file': 'Помилка параметрів: CSV: file,title,artist,album,genre',
        'description': 'Збирає music-pack лише з касетами для Project Zomboid Build 42 і PZ True Music.',
        'done': 'Готово: {path}',
        'dry_run': 'Параметр команди.',
        'dry_run_done': 'Dry-run: мод не збирався',
        'enable_mod': 'У грі ввімкни цей мод разом із PZ True Music / truemusic',
        'example1': 'Параметр команди.',
        'example2': 'Параметр команди.',
        'examples': 'Параметри',
        'ffmpeg_convert': 'ffmpeg: {src} -> {dst}',
        'ffmpeg_failed': 'ffmpeg завершився з помилкою: {error}',
        'ffmpeg_not_found': 'ffmpeg не знайдено. Встанови ffmpeg і переконайся, що він доступний у PATH.',
        'ffprobe_missing': 'Попередження: ffprobe не знайдено, теги не будуть прочитані',
        'folder_exists': 'Папка вже існує: {path}\nДодай --force, щоб оновити мод зі збереженням .ogg, або --reset, щоб видалити все.',
        'force': 'Параметр команди.',
        'found_albums': 'Знайдено альбомів: {count}',
        'found_tracks': 'Знайдено треків: {count}',
        'generic_option': 'Параметр команди.',
        'help': 'Параметр команди.',
        'help_lang': 'Параметр команди.',
        'input': 'Параметр команди.',
        'invalid_album_mode': 'Помилка параметрів: --album-mode',
        'invalid_language': 'Помилка параметрів: language',
        'lang': 'Параметр команди.',
        'language': 'Мова',
        'languages': 'Параметр команди.',
        'make_zip': 'Параметр команди.',
        'manifest_csv': 'Параметр команди.',
        'max_tracks_per_album': 'Параметр команди.',
        'missing_required': 'Не вказано обов’язковий параметр: {name}',
        'mod_id': 'Параметр команди.',
        'mod_id_sanitized': 'ID мода очищено: {old} -> {new}',
        'modversion': 'Параметр команди.',
        'more_albums': '... ще альбомів: {count}',
        'name': 'Параметр команди.',
        'no_audio_files': 'У папці немає аудіофайлів: {path}',
        'no_input_dir': 'Папки з музикою не існує: {path}',
        'optional': 'Параметри',
        'output': 'Параметр команди.',
        'quality': 'Параметр команди.',
        'rebuild_audio': 'Параметр команди.',
        'require_mod': 'Параметр команди.',
        'required': 'Параметри',
        'reset': 'Параметр команди.',
        'skip_audio': 'Параметр команди.',
        'skip_existing': 'пропуск наявного файлу: {item}',
        'spawn': 'Параметр команди.',
        'supported_folders': 'Підтримувані папки перекладів True Music',
        'usage': 'Використання',
        'use_tags': 'Параметр команди.',
        'workshop_layout': 'Параметр команди.',
        'zip_created': 'ZIP: {path}'}}


# Language-specific compact overrides for languages not covered by the detailed help block above.
_CLI_EXTRA = {
    "CA": {"usage":"Ús","optional":"Opcions","required":"Arguments obligatoris","examples":"Exemples","language":"Llengua","description":"Crea un paquet de música només amb cassets per a Project Zomboid Build 42 i PZ True Music.","supported_folders":"Carpetes de traducció True Music compatibles","generic_option":"Opció de l’ordre.","done":"Fet: {path}","found_albums":"Àlbums trobats: {count}","found_tracks":"Pistes trobades: {count}","missing_required":"Falta un argument obligatori: {name}","arg_error":"Error d’arguments: {message}"},
    "CS": {"usage":"Použití","optional":"Volby","required":"Povinné argumenty","examples":"Příklady","language":"Jazyk","description":"Vytvoří hudební balíček pouze s kazetami pro Project Zomboid Build 42 a PZ True Music.","supported_folders":"Podporované složky překladů True Music","generic_option":"Volba příkazu.","done":"Hotovo: {path}","found_albums":"Nalezená alba: {count}","found_tracks":"Nalezené skladby: {count}","missing_required":"Chybí povinný argument: {name}","arg_error":"Chyba argumentů: {message}"},
    "DA": {"usage":"Brug","optional":"Indstillinger","required":"Påkrævede argumenter","examples":"Eksempler","language":"Sprog","description":"Bygger en musikpakke kun med kassettebånd til Project Zomboid Build 42 og PZ True Music.","supported_folders":"Understøttede True Music-oversættelsesmapper","generic_option":"Kommandoindstilling.","done":"Færdig: {path}","found_albums":"Fundne albums: {count}","found_tracks":"Fundne numre: {count}","missing_required":"Manglende påkrævet argument: {name}","arg_error":"Argumentfejl: {message}"},
    "FI": {"usage":"Käyttö","optional":"Valinnat","required":"Pakolliset argumentit","examples":"Esimerkit","language":"Kieli","description":"Luo vain kasetteja sisältävän musiikkipaketin Project Zomboid Build 42:lle ja PZ True Musicille.","supported_folders":"Tuetut True Music -käännöskansiot","generic_option":"Komentoasetus.","done":"Valmis: {path}","found_albums":"Albumeja löytyi: {count}","found_tracks":"Kappaleita löytyi: {count}","missing_required":"Pakollinen argumentti puuttuu: {name}","arg_error":"Argumenttivirhe: {message}"},
    "HU": {"usage":"Használat","optional":"Beállítások","required":"Kötelező argumentumok","examples":"Példák","language":"Nyelv","description":"Csak kazettákat tartalmazó zenei csomagot készít Project Zomboid Build 42 és PZ True Music számára.","supported_folders":"Támogatott True Music fordítási mappák","generic_option":"Parancsopció.","done":"Kész: {path}","found_albums":"Talált albumok: {count}","found_tracks":"Talált számok: {count}","missing_required":"Hiányzó kötelező argumentum: {name}","arg_error":"Argumentumhiba: {message}"},
    "ID": {"usage":"Penggunaan","optional":"Opsi","required":"Argumen wajib","examples":"Contoh","language":"Bahasa","description":"Membuat paket musik khusus kaset untuk Project Zomboid Build 42 dan PZ True Music.","supported_folders":"Folder terjemahan True Music yang didukung","generic_option":"Opsi perintah.","done":"Selesai: {path}","found_albums":"Album ditemukan: {count}","found_tracks":"Trek ditemukan: {count}","missing_required":"Argumen wajib hilang: {name}","arg_error":"Kesalahan argumen: {message}"},
    "NL": {"usage":"Gebruik","optional":"Opties","required":"Vereiste argumenten","examples":"Voorbeelden","language":"Taal","description":"Bouwt een muziekpakket met alleen cassettes voor Project Zomboid Build 42 en PZ True Music.","supported_folders":"Ondersteunde True Music-vertaalmappen","generic_option":"Commando-optie.","done":"Klaar: {path}","found_albums":"Albums gevonden: {count}","found_tracks":"Nummers gevonden: {count}","missing_required":"Vereist argument ontbreekt: {name}","arg_error":"Argumentfout: {message}"},
    "NO": {"usage":"Bruk","optional":"Valg","required":"Påkrevde argumenter","examples":"Eksempler","language":"Språk","description":"Bygger en musikkpakke bare med kassetter for Project Zomboid Build 42 og PZ True Music.","supported_folders":"Støttede True Music-oversettelsesmapper","generic_option":"Kommandoalternativ.","done":"Ferdig: {path}","found_albums":"Album funnet: {count}","found_tracks":"Spor funnet: {count}","missing_required":"Mangler påkrevd argument: {name}","arg_error":"Argumentfeil: {message}"},
    "PH": {"usage":"Paggamit","optional":"Mga opsyon","required":"Kailangang argumento","examples":"Mga halimbawa","language":"Wika","description":"Gumagawa ng cassette-only music pack para sa Project Zomboid Build 42 at PZ True Music.","supported_folders":"Mga suportadong folder ng pagsasalin ng True Music","generic_option":"Opsyon ng command.","done":"Tapos: {path}","found_albums":"Nakitang album: {count}","found_tracks":"Nakitang track: {count}","missing_required":"Kulang ang kailangang argumento: {name}","arg_error":"Error sa argumento: {message}"},
    "RO": {"usage":"Utilizare","optional":"Opțiuni","required":"Argumente obligatorii","examples":"Exemple","language":"Limbă","description":"Creează un pachet muzical doar cu casete pentru Project Zomboid Build 42 și PZ True Music.","supported_folders":"Foldere de traducere True Music acceptate","generic_option":"Opțiune de comandă.","done":"Gata: {path}","found_albums":"Albume găsite: {count}","found_tracks":"Piese găsite: {count}","missing_required":"Lipsește argumentul obligatoriu: {name}","arg_error":"Eroare de argumente: {message}"},
    "TH": {"usage":"วิธีใช้","optional":"ตัวเลือก","required":"อาร์กิวเมนต์ที่จำเป็น","examples":"ตัวอย่าง","language":"ภาษา","description":"สร้างแพ็กเพลงแบบเทปคาสเซ็ตเท่านั้นสำหรับ Project Zomboid Build 42 และ PZ True Music","supported_folders":"โฟลเดอร์แปลภาษา True Music ที่รองรับ","generic_option":"ตัวเลือกคำสั่ง.","done":"เสร็จแล้ว: {path}","found_albums":"พบอัลบั้ม: {count}","found_tracks":"พบแทร็ก: {count}","missing_required":"ขาดอาร์กิวเมนต์ที่จำเป็น: {name}","arg_error":"ข้อผิดพลาดของอาร์กิวเมนต์: {message}"},
}
for _code, _patch in _CLI_EXTRA.items():
    CLI_TRANSLATIONS.setdefault(_code, {}).update(_patch)
    for _key in ("input", "output", "mod_id", "name", "author", "album_name", "album_mode", "use_tags", "manifest_csv", "max_tracks_per_album", "modversion", "require_mod", "spawn", "quality", "copy_ogg", "rebuild_audio", "skip_audio", "languages", "workshop_layout", "make_zip", "dry_run", "force", "reset", "help", "help_lang", "lang", "example1", "example2"):
        CLI_TRANSLATIONS[_code][_key] = CLI_TRANSLATIONS[_code]["generic_option"]


def _safe_format(text: str, **kwargs) -> str:
    try:
        return text.format(**kwargs)
    except Exception:
        return text

def ui(lang: str | None, key: str, **kwargs) -> str:
    lang = normalize_pz_lang(lang)
    pack = CLI_TRANSLATIONS.get(lang, CLI_TRANSLATIONS["EN"])
    text = pack.get(key, CLI_TRANSLATIONS["EN"].get(key, key))
    return _safe_format(text, **kwargs)

def configure_stdio() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except Exception:
            pass


def translit(text: str) -> str:
    text = text.translate(RU_MAP)
    text = unicodedata.normalize("NFKD", text)
    return text.encode("ascii", "ignore").decode("ascii")


def safe_id(text: str, fallback: str = "Id", max_len: int = 90) -> str:
    text = translit(str(text))
    text = re.sub(r"[^A-Za-z0-9]+", "", text)
    if not text:
        text = fallback
    if text[0].isdigit():
        text = fallback + text
    if len(text) > max_len:
        h = hashlib.sha1(text.encode("utf-8")).hexdigest()[:8]
        text = text[: max_len - 8] + h
    return text


def safe_file_stem(text: str, fallback: str = "track", max_len: int = 96) -> str:
    text = translit(str(text))
    text = re.sub(r"[^A-Za-z0-9 ._()\[\]-]+", "", text).strip(" ._")
    text = re.sub(r"\s+", " ", text)
    if not text:
        text = fallback
    if len(text) > max_len:
        h = hashlib.sha1(text.encode("utf-8")).hexdigest()[:8]
        text = text[: max_len - 9].rstrip() + "-" + h
    return text


def lua_quote(text: str) -> str:
    return str(text).replace("\\", "\\\\").replace('"', '\\"')


def pz_script_text(text: str) -> str:
    text = str(text).replace(",", " - ").replace("\n", " ").replace("\r", " ")
    return re.sub(r"\s+", " ", text).strip() or "Untitled"


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def tool_exists(name: str) -> bool:
    return shutil.which(name) is not None


def clean_track_title(stem: str) -> str:
    stem = re.sub(r"^\s*\d{1,3}\s*[-._)]\s*", "", stem)
    return stem.strip() or stem


def normalize_tag_key(tags: dict[str, str], key: str) -> str | None:
    key_low = key.lower()
    for k, v in tags.items():
        if k.lower() == key_low and str(v).strip():
            return str(v).strip()
    return None


def ffprobe_tags(path: Path) -> dict[str, str]:
    if not tool_exists("ffprobe"):
        return {}
    cmd = ["ffprobe", "-v", "error", "-show_entries", "format_tags", "-of", "json", str(path)]
    try:
        proc = subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        data = json.loads(proc.stdout or "{}")
        tags = data.get("format", {}).get("tags", {})
        if isinstance(tags, dict):
            return {str(k): str(v) for k, v in tags.items()}
    except Exception:
        return {}
    return {}


@dataclass
class Track:
    source: Path
    source_rel: str
    title: str
    artist: str
    genre: str
    album_name: str
    album_id: str
    index: int
    global_index: int
    out_filename: str
    cassette_id: str
    cassette_full_item: str
    sound_name: str
    display_key: str


@dataclass
class Album:
    name: str
    album_id: str
    tracks: list[Track] = field(default_factory=list)


def read_manifest(csv_path: Path | None) -> dict[str, dict[str, str]]:
    """Optional CSV override. Supported columns: file,title,artist,album,genre."""
    if not csv_path:
        return {}
    result: dict[str, dict[str, str]] = {}
    with csv_path.open("r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        if not reader.fieldnames or "file" not in reader.fieldnames:
            raise SystemExit(ui(getattr(args, "lang", None), "csv_requires_file"))
        for row in reader:
            file_name = (row.get("file") or "").strip()
            if not file_name:
                continue
            clean = {k: (row.get(k) or "").strip() for k in ("title", "artist", "album", "genre")}
            result[file_name] = clean
            result[Path(file_name).name] = clean
    return result


def choose_album_name(src: Path, input_dir: Path, mode: str, tags: dict[str, str], override: dict[str, str], default_album: str) -> str:
    if override.get("album"):
        return override["album"]
    tag_album = normalize_tag_key(tags, "album")
    if mode == "tags" and tag_album:
        return tag_album
    rel_parent = src.parent.relative_to(input_dir)
    parts = rel_parent.parts
    if mode == "root":
        return default_album
    if mode == "top-folder":
        return parts[0] if parts else default_album
    return src.parent.name if parts else default_album


def collect_audio(input_dir: Path, args: argparse.Namespace) -> list[Album]:
    files = sorted(p for p in input_dir.rglob("*") if p.is_file() and p.suffix.lower() in AUDIO_EXTS)
    if not files:
        raise SystemExit(ui(getattr(args, "lang", None), "no_audio_files", path=input_dir))

    manifest = read_manifest(Path(args.manifest_csv).expanduser().resolve() if args.manifest_csv else None)

    raw_tracks: list[dict[str, object]] = []
    for src in files:
        rel = str(src.relative_to(input_dir))
        override = manifest.get(str(src), manifest.get(rel, manifest.get(src.name, {})))
        tags = ffprobe_tags(src) if args.use_tags or args.album_mode == "tags" else {}

        tag_title = normalize_tag_key(tags, "title")
        tag_artist = normalize_tag_key(tags, "artist") or normalize_tag_key(tags, "album_artist")
        tag_genre = normalize_tag_key(tags, "genre")

        title = override.get("title") or (tag_title if args.use_tags else None) or clean_track_title(src.stem)
        artist = override.get("artist") or (tag_artist if args.use_tags else None) or ""
        genre = override.get("genre") or (tag_genre if args.use_tags else None) or ""
        album_name = choose_album_name(src, input_dir, args.album_mode, tags, override, args.album_name)

        raw_tracks.append({
            "source": src,
            "source_rel": rel,
            "title": str(title).strip(),
            "artist": str(artist).strip(),
            "genre": str(genre).strip(),
            "album_name": str(album_name).strip() or args.album_name,
        })

    grouped: dict[str, list[dict[str, object]]] = {}
    for t in raw_tracks:
        grouped.setdefault(str(t["album_name"]), []).append(t)

    albums: list[Album] = []
    used_album_ids: set[str] = set()

    # Create albums/chunks first.
    album_chunks: list[tuple[Album, list[dict[str, object]]]] = []
    for album_index, (album_name, items) in enumerate(sorted(grouped.items(), key=lambda kv: safe_file_stem(kv[0]).lower()), start=1):
        chunks: list[tuple[str, list[dict[str, object]]]] = []
        if args.max_tracks_per_album and args.max_tracks_per_album > 0 and len(items) > args.max_tracks_per_album:
            for part_index in range(0, len(items), args.max_tracks_per_album):
                part_num = part_index // args.max_tracks_per_album + 1
                chunks.append((f"{album_name} Part {part_num}", items[part_index:part_index + args.max_tracks_per_album]))
        else:
            chunks.append((album_name, items))

        for chunk_name, chunk_items in chunks:
            base_album_id = safe_id(chunk_name, fallback=f"Album{album_index}", max_len=58)
            album_id = base_album_id
            n = 2
            while album_id in used_album_ids:
                album_id = f"{base_album_id}{n}"
                n += 1
            used_album_ids.add(album_id)
            album = Album(name=chunk_name, album_id=album_id)
            albums.append(album)
            album_chunks.append((album, chunk_items))

    used_item_ids: set[str] = set()
    used_filenames_by_album: dict[str, set[str]] = {}
    global_index = 0
    mod_prefix = safe_id(args.mod_id, fallback="Pack", max_len=22)

    for album, chunk_items in album_chunks:
        used_files = used_filenames_by_album.setdefault(album.album_id, set())
        for idx, raw in enumerate(sorted(chunk_items, key=lambda x: str(x["source"]).lower()), start=1):
            global_index += 1
            src = raw["source"]
            assert isinstance(src, Path)
            source_rel = str(raw["source_rel"])
            artist = str(raw["artist"])
            title = str(raw["title"])
            genre = str(raw["genre"])
            display_title = f"{artist} - {title}" if artist and artist.lower() not in title.lower() else title

            file_stem = safe_file_stem(display_title, fallback=f"Track{idx:03d}")
            out_name = f"{idx:03d} - {file_stem}.ogg"
            if out_name in used_files:
                out_name = f"{idx:03d} - {file_stem}-{hashlib.sha1(source_rel.encode()).hexdigest()[:6]}.ogg"
            used_files.add(out_name)

            album_prefix = safe_id(album.album_id, fallback="Album", max_len=24)
            track_hash = hashlib.sha1(f"{source_rel}|{display_title}".encode("utf-8")).hexdigest()[:8]
            cassette_id = f"Cassette{mod_prefix}{album_prefix}T{idx:03d}{track_hash}"
            base_item = cassette_id
            dupe = 2
            while cassette_id in used_item_ids:
                cassette_id = f"{base_item}{dupe}"
                dupe += 1
            used_item_ids.add(cassette_id)

            track = Track(
                source=src,
                source_rel=source_rel,
                title=display_title,
                artist=artist,
                genre=genre,
                album_name=album.name,
                album_id=album.album_id,
                index=idx,
                global_index=global_index,
                out_filename=out_name,
                cassette_id=cassette_id,
                cassette_full_item=f"Tsarcraft.{cassette_id}",
                sound_name=cassette_id,
                display_key=f"IGUI_{args.mod_id}_{album.album_id}_Track{idx}",
            )
            album.tracks.append(track)

    return albums


def convert_or_copy_audio(albums: list[Album], media_dir: Path, quality: int, copy_ogg: bool, rebuild_audio: bool, args: argparse.Namespace) -> None:
    for album in albums:
        sound_dir = media_dir / "sound" / "custom_true_music" / album.album_id
        sound_dir.mkdir(parents=True, exist_ok=True)
        for track in album.tracks:
            dst = sound_dir / track.out_filename
            if dst.exists() and dst.stat().st_size > 0 and not rebuild_audio:
                print(ui(getattr(args, "lang", None), "skip_existing", item=f"{album.album_id}/{dst.name}"))
                continue

            if track.source.suffix.lower() == ".ogg" and copy_ogg:
                shutil.copy2(track.source, dst)
                print(ui(getattr(args, "lang", None), "copy_audio", src=track.source.name, dst=f"{album.album_id}/{dst.name}"))
                continue

            cmd = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                "-i", str(track.source),
                "-vn", "-map_metadata", "0",
                "-c:a", "libvorbis", "-q:a", str(quality),
                str(dst),
            ]
            print(ui(getattr(args, "lang", None), "ffmpeg_convert", src=track.source.name, dst=f"{album.album_id}/{dst.name}"))
            subprocess.run(cmd, check=True)


def generate_mod_info(args: argparse.Namespace, albums: list[Album]) -> str:
    total = sum(len(a.tracks) for a in albums)
    lines = [
        f"name={args.name}",
        f"id={args.mod_id}",
        f"author={args.author}",
        "versionMin=42.13.0",
        f"modversion={args.modversion}",
    ]
    if args.require_mod:
        lines.append(f"require={args.require_mod}")
    lines += [
        "description=Generated cassette-only B42 music pack for PZ True Music <LINE>",
        f"description=Albums: {len(albums)} <LINE>",
        f"description=Tracks: {total} <LINE>",
    ]
    for album in albums[:120]:
        lines.append(f"description={album.name}: {len(album.tracks)} tracks <BR>")
    if len(albums) > 120:
        lines.append(f"description=... and {len(albums) - 120} more albums <BR>")
    return "\n".join(lines) + "\n"


def generate_sandbox_options(args: argparse.Namespace, albums: list[Album]) -> str:
    parts = ["VERSION = 1,", ""]
    for album in albums:
        parts.append(f"option {args.mod_id}_TrueMusic.{album.album_id}")
        parts.append("{")
        parts.append("\ttype = boolean,")
        parts.append("\tdefault = true,")
        parts.append(f"\tpage = {args.mod_id}_TrueMusic,")
        parts.append(f"\ttranslation = {args.mod_id}_TrueMusic_{album.album_id},")
        parts.append("}")
        parts.append("")
    parts.append(f"option {args.mod_id}_TrueMusic.musicSpawn")
    parts.append("{")
    parts.append("\ttype = integer,")
    parts.append("\tmin = 1,")
    parts.append("\tmax = 1000,")
    parts.append(f"\tdefault = {args.spawn},")
    parts.append(f"\tpage = {args.mod_id}_TrueMusic,")
    parts.append(f"\ttranslation = {args.mod_id}_musicSpawn,")
    parts.append("}")
    return "\n".join(parts) + "\n"


def generate_cassette_sounds(albums: list[Album]) -> str:
    parts = ["module Tsarcraft", "{", ""]
    for album in albums:
        sound_rel_dir = f"media/sound/custom_true_music/{album.album_id}"
        for t in album.tracks:
            parts.append(f"\tsound {t.sound_name}")
            parts.append("\t{")
            parts.append("\t\tcategory = True Music,")
            parts.append("\t\tmaster = Ambient,")
            parts.append("\t\tclip")
            parts.append("\t\t{")
            parts.append(f"\t\t\tfile = {sound_rel_dir}/{t.out_filename},")
            parts.append("\t\t\tdistanceMax = 75,")
            parts.append("\t\t}")
            parts.append("\t}")
            parts.append("")
    parts.append("}")
    return "\n".join(parts) + "\n"


def generate_cassette_items(albums: list[Album]) -> str:
    parts = [
        "module Tsarcraft",
        "{",
        "\timports",
        "\t{",
        "\t\tBase",
        "\t}",
        "",
        "/********************Generated PZ True Music Cassettes********************/",
        "",
    ]
    i = 0
    for album in albums:
        for t in album.tracks:
            i += 1
            icon_num = ((i - 1) % 11) + 1
            display_name = pz_script_text(f"Cassette {t.title}")
            parts.append(f"\titem {t.cassette_id}")
            parts.append("\t{")
            parts.append("\t\tItemType\t\t\t= base:normal,")
            parts.append("\t\tDisplayCategory\t\t= Entertainment,")
            parts.append("\t\tWeight\t\t\t\t= 0.02,")
            parts.append(f"\t\tIcon\t\t\t\t= TCTape{icon_num},")
            parts.append(f"\t\tDisplayName\t\t= {display_name},")
            parts.append(f"\t\tWorldStaticModel\t= Tsarcraft.TCTape{icon_num},")
            parts.append("\t\tTags\t\t\t\t= base:music,")
            parts.append("\t\tCanSpawn\t\t\t= true,")
            parts.append("\t}")
            parts.append("")
    parts.append("}")
    return "\n".join(parts) + "\n"


def generate_cassette_music_defs(albums: list[Album]) -> str:
    parts = [
        "if GlobalMusic == nil then GlobalMusic = {} end",
        "if TCMusic == nil then TCMusic = {} end",
        "if TCMusic.WorldMusicPlayer == nil then TCMusic.WorldMusicPlayer = {} end",
        "",
        "TCMusic.WorldMusicPlayer[\"tsarcraft_music_01_62\"] = \"tsarcraft_music_01_62\"",
        "",
    ]
    for album in albums:
        for t in album.tracks:
            # Some builds/mod forks look up short item name, others full module.item name.
            parts.append(f"GlobalMusic[\"{t.cassette_id}\"] = \"tsarcraft_music_01_62\"")
            parts.append(f"GlobalMusic[\"{t.cassette_full_item}\"] = \"tsarcraft_music_01_62\"")
    return "\n".join(parts) + "\n"


def lua_list(name: str, items: list[str]) -> str:
    lines = [f"local {name} = {{"]
    for item in items:
        lines.append(f"\t\"{lua_quote(item)}\",")
    lines.append("}")
    return "\n".join(lines)


def generate_spawn_lua(args: argparse.Namespace, albums: list[Album]) -> str:
    parts = [
        lua_list("distNames", DIST_NAMES),
        "",
        lua_list("distVehiclesNames", VEHICLE_DIST_NAMES),
        "",
        "local albumItems = {}",
    ]

    for album in albums:
        items = [t.cassette_full_item for t in album.tracks]
        parts.append(lua_list(f"items_{album.album_id}", items))
        parts.append(f"albumItems[\"{album.album_id}\"] = items_{album.album_id}")
        parts.append("")

    parts += [
        f"local sandboxOptions = SandboxVars.{args.mod_id}_TrueMusic or {{}}",
        f"local musicSpawn = (sandboxOptions.musicSpawn or {args.spawn}) * 0.1",
        "",
        "local function addItemsToDistribution(dist, items)",
        "\tif dist and dist.items then",
        "\t\tfor _, itemId in ipairs(items) do",
        "\t\t\ttable.insert(dist.items, itemId)",
        "\t\t\ttable.insert(dist.items, musicSpawn)",
        "\t\tend",
        "\tend",
        "end",
        "",
        "for albumId, items in pairs(albumItems) do",
        "\tlocal lootEnabled = sandboxOptions[albumId]",
        "\tif lootEnabled == nil then lootEnabled = true end",
        "\tif lootEnabled then",
        "\t\tif ProceduralDistributions and ProceduralDistributions.list then",
        "\t\t\tfor _, dist in ipairs(distNames) do",
        "\t\t\t\taddItemsToDistribution(ProceduralDistributions.list[dist], items)",
        "\t\t\tend",
        "\t\tend",
        "",
        "\t\tif VehicleDistributions then",
        "\t\t\tfor _, loc in ipairs(distVehiclesNames) do",
        "\t\t\t\taddItemsToDistribution(VehicleDistributions[loc], items)",
        "\t\t\tend",
        "\t\tend",
        "\tend",
        "end",
    ]
    return "\n".join(parts) + "\n"


def generate_translation_jsons(args: argparse.Namespace, albums: list[Album], lang: str) -> tuple[dict[str, str], dict[str, str], dict[str, str]]:
    lang = normalize_pz_lang(lang)
    cassette = CASSETTE_WORD.get(lang, CASSETTE_WORD["EN"])
    spawn_chance = SPAWN_CHANCE_TEXT.get(lang, SPAWN_CHANCE_TEXT["EN"])
    spawn_album = SPAWN_ALBUM_TEXT.get(lang, SPAWN_ALBUM_TEXT["EN"])

    ig_ui: dict[str, str] = {}
    item_name: dict[str, str] = {}
    sandbox: dict[str, str] = {
        f"Sandbox_{args.mod_id}_TrueMusic": args.name,
        f"Sandbox_{args.mod_id}_musicSpawn": f"{spawn_chance}: {args.spawn * 0.1:g}",
    }

    for album in albums:
        sandbox[f"Sandbox_{args.mod_id}_TrueMusic_{album.album_id}"] = f"{spawn_album} {album.name}"
        for t in album.tracks:
            ig_ui[t.display_key] = t.title
            item_name[t.cassette_full_item] = f"{cassette} {t.title}"
    return ig_ui, item_name, sandbox

def dump_json(data: dict[str, str]) -> str:
    return json.dumps(data, ensure_ascii=False, indent="\t") + "\n"


def write_manifest(mod_root: Path, albums: list[Album]) -> None:
    manifest_path = mod_root / "track_manifest.csv"
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with manifest_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["album", "album_id", "index", "title", "artist", "genre", "source", "ogg_file", "sound_name", "cassette_item"])
        for album in albums:
            for t in album.tracks:
                writer.writerow([album.name, album.album_id, t.index, t.title, t.artist, t.genre, str(t.source), t.out_filename, t.sound_name, t.cassette_full_item])


def zip_dir(src_dir: Path, zip_path: Path) -> None:
    if zip_path.exists():
        zip_path.unlink()
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for p in sorted(src_dir.rglob("*")):
            if p.is_file():
                zf.write(p, p.relative_to(src_dir.parent))


def clean_generated_files(mod_root: Path) -> None:
    """Remove generated text/script files but keep media/sound, so audio cache survives rebuilds."""
    b42 = mod_root / "42"
    media = b42 / "media"
    for rel in [
        "scripts/generated/sounds",
        "scripts/generated/items",
        "lua/shared/Translate",
        "lua/shared",
        "lua/server/items",
    ]:
        p = media / rel
        if p.exists():
            shutil.rmtree(p)
    for p in [b42 / "mod.info", media / "sandbox-options.txt", mod_root / "track_manifest.csv"]:
        if p.exists():
            p.unlink()


def build(args: argparse.Namespace) -> None:
    input_dir = Path(args.input).expanduser().resolve()
    out_dir = Path(args.output).expanduser().resolve()
    if not input_dir.is_dir():
        raise SystemExit(ui(args.lang, "no_input_dir", path=input_dir))
    if not args.skip_audio and not tool_exists("ffmpeg"):
        raise SystemExit(ui(args.lang, "ffmpeg_not_found"))
    if (args.use_tags or args.album_mode == "tags") and not tool_exists("ffprobe"):
        print(ui(args.lang, "ffprobe_missing"), file=sys.stderr)

    old_mod_id = args.mod_id
    args.mod_id = safe_id(args.mod_id, fallback="MusicPack", max_len=60)
    if args.mod_id != old_mod_id:
        print(ui(args.lang, "mod_id_sanitized", old=old_mod_id, new=args.mod_id), file=sys.stderr)

    albums = collect_audio(input_dir, args)
    total_tracks = sum(len(a.tracks) for a in albums)

    print(ui(args.lang, "found_albums", count=len(albums)))
    print(ui(args.lang, "found_tracks", count=total_tracks))
    for album in albums[:80]:
        print(f"- {album.name} [{album.album_id}]: {len(album.tracks)}")
    if len(albums) > 80:
        print(ui(args.lang, "more_albums", count=len(albums) - 80))

    if args.dry_run:
        print(ui(args.lang, "dry_run_done"))
        return

    if args.workshop_layout:
        mod_root = out_dir / args.mod_id / "Contents" / "mods" / args.mod_id
        package_root = out_dir / args.mod_id
    else:
        mod_root = out_dir / args.mod_id
        package_root = mod_root

    if mod_root.exists() and args.reset:
        shutil.rmtree(mod_root)
    elif mod_root.exists() and not args.force:
        raise SystemExit(ui(args.lang, "folder_exists", path=mod_root))
    elif mod_root.exists() and args.force:
        clean_generated_files(mod_root)

    common_dir = mod_root / "common"
    b42_dir = mod_root / "42"
    media_dir = b42_dir / "media"
    common_dir.mkdir(parents=True, exist_ok=True)
    b42_dir.mkdir(parents=True, exist_ok=True)

    if not args.skip_audio:
        convert_or_copy_audio(albums, media_dir, args.quality, args.copy_ogg, args.rebuild_audio, args)

    write_text(b42_dir / "mod.info", generate_mod_info(args, albums))
    write_text(media_dir / "sandbox-options.txt", generate_sandbox_options(args, albums))
    write_text(media_dir / "scripts/generated/sounds" / f"TCGSoundsTCBoombox{args.mod_id}.txt", generate_cassette_sounds(albums))
    write_text(media_dir / "scripts/generated/items" / f"TCMusicScriptTCBoombox{args.mod_id}.txt", generate_cassette_items(albums))
    write_text(media_dir / "lua/shared" / f"TCGMusicDefenitionsTCBoombox{args.mod_id}.lua", generate_cassette_music_defs(albums))
    write_text(media_dir / "lua/server/items" / f"TCLoading{args.mod_id}.lua", generate_spawn_lua(args, albums))

    for lang in args.languages:
        lang = normalize_pz_lang(lang)
        ig_ui, item_name, sandbox = generate_translation_jsons(args, albums, lang)
        translate_dir = media_dir / "lua/shared/Translate" / lang
        write_text(translate_dir / "IG_UI.json", dump_json(ig_ui))
        write_text(translate_dir / "ItemName.json", dump_json(item_name))
        write_text(translate_dir / "Sandbox.json", dump_json(sandbox))

    write_manifest(mod_root, albums)

    if args.make_zip:
        zip_path = out_dir / f"{args.mod_id}.zip"
        zip_dir(package_root, zip_path)
        print(ui(args.lang, "zip_created", path=zip_path))

    print(ui(args.lang, "done", path=package_root))
    print(ui(args.lang, "enable_mod"))


def normalize_pz_lang(value: str | None) -> str:
    if not value:
        return "EN"
    value = value.strip().replace("-", "_")
    if not value:
        return "EN"
    raw = value.split(".")[0].lower()
    if raw in {"c", "posix"}:
        return "EN"
    # Direct True Music/PZ code, for example RU or PTBR.
    upper = raw.replace("_", "").upper()
    if upper in TRUE_MUSIC_LANGS:
        return upper
    if raw in LOCALE_TO_PZ_LANG:
        return LOCALE_TO_PZ_LANG[raw]
    base = raw.split("_")[0]
    return LOCALE_TO_PZ_LANG.get(base, "EN")


def detect_help_lang(argv: list[str]) -> str:
    # Explicit override has priority and is useful for testing all localizations.
    for i, arg in enumerate(argv):
        if arg == "--help-lang" and i + 1 < len(argv):
            return normalize_pz_lang(argv[i + 1])
        if arg.startswith("--help-lang="):
            return normalize_pz_lang(arg.split("=", 1)[1])

    for env_name in ("PZ_HELP_LANG", "LC_ALL", "LC_MESSAGES", "LANGUAGE", "LANG"):
        value = os.environ.get(env_name)
        if value:
            # LANGUAGE can look like ru:en_US:en.
            return normalize_pz_lang(value.split(":", 1)[0])

    try:
        loc = locale.getlocale()[0]
    except Exception:
        loc = None
    return normalize_pz_lang(loc)


def help_text(lang: str, key: str) -> str:
    lang = normalize_pz_lang(lang)
    if lang in HELP_TRANSLATIONS and key in HELP_TRANSLATIONS[lang]:
        return HELP_TRANSLATIONS[lang][key]
    if key in CLI_TRANSLATIONS.get(lang, {}):
        return CLI_TRANSLATIONS[lang][key]
    real_lang = lang if lang in HELP_TRANSLATIONS else HELP_FALLBACKS.get(lang, "EN")
    return HELP_TRANSLATIONS.get(real_lang, HELP_TRANSLATIONS["EN"]).get(key, CLI_TRANSLATIONS.get(lang, CLI_TRANSLATIONS["EN"]).get("generic_option", key))


def print_localized_help(lang: str) -> None:
    lang = normalize_pz_lang(lang)
    t = lambda key: help_text(lang, key)
    script = Path(sys.argv[0]).name or "pz_b42_true_music_cassette_builder.py"

    rows_required = [
        ("-i, --input DIR", t("input")),
        ("--mod-id ID", t("mod_id")),
        ("--name NAME", t("name")),
    ]
    rows_optional = [
        ("-o, --output DIR", t("output")),
        ("--author NAME", t("author")),
        ("--album-name NAME", t("album_name")),
        ("--album-mode {leaf-folder,top-folder,root,tags}", t("album_mode")),
        ("--use-tags", t("use_tags")),
        ("--manifest-csv FILE", t("manifest_csv")),
        ("--max-tracks-per-album N", t("max_tracks_per_album")),
        ("--modversion VERSION", t("modversion")),
        ("--require-mod MODID", t("require_mod")),
        ("--spawn N", t("spawn")),
        ("--quality N", t("quality")),
        ("--copy-ogg", t("copy_ogg")),
        ("--rebuild-audio", t("rebuild_audio")),
        ("--skip-audio", t("skip_audio")),
        ("--languages LANG [LANG ...]", t("languages")),
        ("--workshop-layout", t("workshop_layout")),
        ("--make-zip", t("make_zip")),
        ("--dry-run", t("dry_run")),
        ("--force", t("force")),
        ("--reset", t("reset")),
        ("--help, -h", t("help")),
        ("--help-lang LANG", t("help_lang")),
        ("--lang LANG", t("lang")),
    ]

    print(f"{t('usage')}: {script} -i DIR --mod-id ID --name NAME [options]\n")
    print(t("description"))
    print(f"{t('language')}: {lang} ({LANG_DISPLAY_NAMES.get(lang, 'Unknown')})\n")

    def print_rows(title: str, rows: list[tuple[str, str]]) -> None:
        print(title + ":")
        width = max(len(flag) for flag, _ in rows) + 2
        for flag, desc in rows:
            wrapped = textwrap.wrap(desc, width=96 - width) or [""]
            print(f"  {flag:<{width}}{wrapped[0]}")
            for line in wrapped[1:]:
                print("  " + " " * width + line)
        print()

    print_rows(t("required"), rows_required)
    print_rows(t("optional"), rows_optional)
    print(t("examples") + ":")
    print("  " + t("example1"))
    print(f"  python {script} --input ~/Музыка_ogg --output ~/Zomboid/mods --mod-id MusicPack --name \"Music Pack\" --copy-ogg --force")
    print("  " + t("example2"))
    print(f"  python {script} --help --help-lang {lang}\n")
    print(t("supported_folders") + ":")
    print("  " + " ".join(TRUE_MUSIC_LANGS))


def create_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Build a cassette-only Project Zomboid B42 music pack for PZ True Music",
        add_help=False,
    )
    p.add_argument("--help", "-h", action="store_true")
    p.add_argument("--help-lang")
    p.add_argument("--lang")
    p.add_argument("--input", "-i")
    p.add_argument("--output", "-o", default="./build")
    p.add_argument("--mod-id")
    p.add_argument("--name")
    p.add_argument("--author", default="Average User")
    p.add_argument("--album-name", default="Custom Album")
    p.add_argument("--album-mode", default="leaf-folder")
    p.add_argument("--use-tags", action="store_true")
    p.add_argument("--manifest-csv")
    p.add_argument("--max-tracks-per-album", type=int, default=180)
    p.add_argument("--modversion", default="1.0")
    p.add_argument("--require-mod", default="truemusic")
    p.add_argument("--spawn", type=int, default=5)
    p.add_argument("--quality", type=int, default=4)
    p.add_argument("--copy-ogg", action="store_true")
    p.add_argument("--rebuild-audio", action="store_true")
    p.add_argument("--skip-audio", action="store_true")
    p.add_argument("--languages", nargs="+", default=TRUE_MUSIC_LANGS)
    p.add_argument("--workshop-layout", action="store_true")
    p.add_argument("--make-zip", action="store_true")
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("--force", action="store_true")
    p.add_argument("--reset", action="store_true")
    return p


def parse_args(argv: list[str]) -> argparse.Namespace:
    detected_lang = detect_help_lang(argv)
    if "--help" in argv or "-h" in argv:
        print_localized_help(detected_lang)
        raise SystemExit(0)

    parser = create_parser()
    try:
        args = parser.parse_args(argv)
    except SystemExit as exc:
        raise SystemExit(ui(detected_lang, "arg_error", message=str(exc))) from exc

    args.lang = normalize_pz_lang(args.lang or args.help_lang or detected_lang)
    for attr, flag in (("input", "--input"), ("mod_id", "--mod-id"), ("name", "--name")):
        if not getattr(args, attr):
            raise SystemExit(ui(args.lang, "missing_required", name=flag))

    if args.album_mode not in {"leaf-folder", "top-folder", "root", "tags"}:
        raise SystemExit(ui(args.lang, "invalid_album_mode", value=args.album_mode))

    args.languages = [normalize_pz_lang(x) for x in args.languages]
    args.languages = list(dict.fromkeys(args.languages))
    return args

if __name__ == "__main__":
    configure_stdio()
    try:
        build(parse_args(sys.argv[1:]))
    except subprocess.CalledProcessError as e:
        raise SystemExit(ui(detect_help_lang(sys.argv[1:]), "ffmpeg_failed", error=e)) from e
