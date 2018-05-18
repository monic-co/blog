import React from 'react'
import Link from 'gatsby-link'
import { fontFace, injectGlobal } from "emotion"
import styled from "react-emotion"

injectGlobal`
  * {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
  }

  body {
    background-color: #f4f5f6;
    color: #0a2e6b;
    font-family: proxima-nova, Nunino, sans-serif;
  }

  h2, h3 {
    font-weight: 300;
    margin: 30px 0;
  }

  p, ul {
    font-size: 14pt;
    line-height: 1.55;
  }

  li {
    margin-left: 20px;
  }

  pre, code {
    font-size: 11pt;
  }

  a {
    text-decoration: none;
  }
`

require("./theme.css");

class Template extends React.Component {
  render() {
    const { location, children } = this.props
    let header

    let rootPath = `/`
    if (typeof __PREFIX_PATHS__ !== `undefined` && __PREFIX_PATHS__) {
      rootPath = __PATH_PREFIX__ + `/`
    }

    if (location.pathname === rootPath) {
      header = (
        <h1
          style={{
            // ...scale(1.5),
            fontFamily: 'Nunino, sans-serif',
            fontWeight: 300,
            marginTop: 0,
            marginBottom: 100,
          }}
        >
          <Link
            style={{
              boxShadow: 'none',
              textDecoration: 'none',
              color: 'inherit',
            }}
            to={'/'}
          >
            MONIC Blog
          </Link>
        </h1>
      )
    } else {
      header = (
        <h3
          style={{
            fontFamily: 'Nunino, sans-serif',
            fontWeight: 400,
            marginTop: 0,
            marginBottom: 75,
          }}
        >
          <Link
            style={{
              boxShadow: 'none',
              textDecoration: 'none',
              color: 'inherit',
            }}
            to={'/'}
          >
            MONIC Blog
          </Link>
        </h3>
      )
    }
    return (
      <div
        style={{
        }}
      >
        <header style={{margin: '3vw auto', display: 'flex', justifyContent: 'center'}}>
          <div>
            {header}
          </div>
        </header>
        <div style={{
          maxWidth: 1200,
          margin: 'auto',
        }}>
          {children()}
        </div>
      </div>
    )
  }
}

export default Template
