export interface DockerContainerListEntry {
  ID: string;
  Names: string;
  State: string;
  Status: string;
  Image: string;
  CreatedAt: string;
  Ports?: string;
}

export interface PodmanContainerListEntry {
  Id: string;
  Names: string[];
  State: string;
  Status: string;
  Image: string;
  CreatedAt: number;
  Ports?: string;
}

export interface DockerImageListEntry {
  ID: string;
  Repository: string;
  Tag: string;
  Digest?: string;
  Size: string;
  CreatedAt: string;
}

export interface PodmanImageListEntry {
  Id: string;
  Repository: string;
  Tag: string;
  Digest?: string;
  Size: number;
  Created: number;
  Labels?: Record<string, string>;
}

export interface DockerVolumeListEntry {
  Name: string;
  Driver: string;
  Mountpoint: string;
  Labels?: Record<string, string>;
  Size?: number;
}

export interface PodmanVolumeListEntry {
  Name: string;
  Driver: string;
  Mountpoint: string;
  Labels?: Record<string, string>;
  Size?: number;
}

export interface DockerNetworkListEntry {
  ID: string;
  Name: string;
  Driver: string;
  Labels?: Record<string, string>;
}

export interface PodmanNetworkListEntry {
  NetworkID: string;
  Name: string;
  Driver: string;
  Labels?: Record<string, string>;
}
